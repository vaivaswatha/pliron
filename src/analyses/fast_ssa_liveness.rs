//! Fast liveness queries on an SSA-CFG.

use core::panic;

use rustc_hash::FxHashMap;

use crate::{
    basic_block::BasicBlock,
    context::{Context, Ptr},
    graph::{
        ControlFlowGraph,
        dominance::{DomInfo, DomTree},
        find_ancestor_block_in_region,
        traversals::region::{DFSEdgeKind, DFSTraversal},
    },
    irbuild::inserter::OpInsertionPoint,
    linked_list::{ContainsLinkedList, LinkedList},
    region::Region,
    value::Value,
};

type BitSet = hi_sparse_bitset::BitSet<hi_sparse_bitset::config::_128bit>;
use hi_sparse_bitset::{ops as bitset_ops, reduce as bitset_reduce};

/// This mirrors the approach from "Fast Liveness Checking for SSA-Form Programs":
/// reduced reachability (`R`) and back-edge target closure (`Tq`) are precomputed
/// per region and reused across value queries.
pub struct LivenessTq {
    /// The region this info is associated with.
    region: Ptr<Region>,
    /// Is this region's CFG reducible?
    is_reducible: bool,
    /// Strict dominator subtree for each block in the region
    sdom_tree: Vec<BitSet>,
    /// Maps a block to its index in `blocks` for quick lookup.
    block_to_index: FxHashMap<Ptr<BasicBlock>, usize>,
    /// For each block, the set of blocks reachable from it in the reduced CFG
    /// (i.e. excluding back edges).
    reduced_reachability: Vec<BitSet>,
    /// For each block, the set of back-edge targets reachable from it.
    tq_sets: Vec<BitSet>,
    /// The set of blocks that are targets of back edges, for quick lookup.
    back_edge_targets: BitSet,
}

impl LivenessTq {
    fn new(ctx: &Context, region: Ptr<Region>, dom_tree: &DomTree<Ptr<Region>, Context>) -> Self {
        let dfs = DFSTraversal::new(ctx, &region);
        // RPO ordered blocks reachable from entry and a
        // map from `Ptr<BasicBlock>` to its index in `blocks` for quick lookup.
        let (blocks, block_to_index) = dfs
            .reverse_post_order()
            .enumerate()
            .map(|(i, block)| (block, (block, i)))
            .unzip::<_, _, Vec<_>, FxHashMap<_, _>>();

        let sdom_tree = Self::dom_tree_to_sdom_tree(&block_to_index, dom_tree);

        // Successors in the reduced CFG (i.e. excluding back edges)
        // are collected to compute reduced reachability.
        let mut reduced_successors = vec![BitSet::default(); blocks.len()];
        let mut back_edge_targets = BitSet::default();
        let mut back_edges_by_source = vec![Vec::<usize>::new(); blocks.len()];

        let mut is_reducible = true;
        for (src_idx, src_block) in blocks.iter().enumerate() {
            for succ in region.successors(ctx, src_block) {
                let dst_idx = *block_to_index
                    .get(&succ)
                    .expect("Successor blocks must be in the same region and reachable from entry");

                let edge_kind = dfs.edge_kind(src_block, &succ);
                if edge_kind == DFSEdgeKind::Back {
                    back_edges_by_source[src_idx].push(dst_idx);
                    back_edge_targets.insert(dst_idx);
                    if dst_idx != src_idx && !sdom_tree[dst_idx].contains(src_idx) {
                        // If the back edge goes to a non-dominator, then the CFG is irreducible.
                        // Note: self-loops (dst_idx == src_idx) are always reducible since the
                        // target trivially dominates the source (reflexive dominance).
                        is_reducible = false;
                    }
                } else {
                    reduced_successors[src_idx].insert(dst_idx);
                }
            }
        }

        // Compute reduced reachability for all nodes.
        let reduced_reachability = Self::compute_reduced_reachability(&reduced_successors);
        // Compute T_up sets for all nodes.
        let t_up_sets = Self::compute_t_up_sets(&reduced_reachability, &back_edges_by_source);

        let dfs_preorder: Vec<_> = dfs
            .pre_order()
            .map(|block| block_to_index[&block])
            .collect();
        let dfs_postorder: Vec<_> = blocks
            .iter()
            .rev()
            .map(|block| block_to_index[block])
            .collect();
        // Compute Tq sets for all nodes.
        let tq_sets = Self::compute_tq_sets(
            &t_up_sets,
            &reduced_successors,
            &back_edges_by_source,
            &back_edge_targets,
            &dfs_preorder,
            &dfs_postorder,
        );

        Self {
            region,
            sdom_tree,
            block_to_index,
            reduced_reachability,
            tq_sets,
            back_edge_targets,
            is_reducible,
        }
    }

    // Compute the strict dominator sub-tree for each node.
    fn dom_tree_to_sdom_tree(
        block_to_index: &FxHashMap<Ptr<BasicBlock>, usize>,
        dom_tree: &DomTree<Ptr<Region>, Context>,
    ) -> Vec<BitSet> {
        let mut sdom_tree = vec![BitSet::default(); block_to_index.len()];

        fn recurser(
            sdom_tree: &mut [BitSet],
            block_to_index: &FxHashMap<Ptr<BasicBlock>, usize>,
            dom_tree: &DomTree<Ptr<Region>, Context>,
            block: Ptr<BasicBlock>,
        ) {
            let block_idx = block_to_index[&block];
            let children = dom_tree.children(&block).collect::<Vec<_>>();
            let mut child_indices = Vec::with_capacity(children.len());

            // Compute sdom_tree for each child.
            for &child in &children {
                recurser(sdom_tree, block_to_index, dom_tree, child);
                let child_idx = block_to_index[&child];
                child_indices.push(child_idx);
            }

            // Union the sdom_tree of all children.
            let children_sdom_tree = child_indices.iter().map(|&child_idx| &sdom_tree[child_idx]);
            // Add the children themselves
            let children_nodes: BitSet = child_indices.iter().copied().collect();
            // Union of children's sdom_tree plus the children themselves is the sdom_tree for this node.
            let subtree = bitset_reduce(bitset_ops::Or, children_sdom_tree);
            sdom_tree[block_idx] =
                (&subtree.map(Into::<BitSet>::into).unwrap_or_default() | &children_nodes).into();
        }
        let root = dom_tree
            .root()
            .expect("Dominator tree must have a root corresponding to the region entry block");
        recurser(&mut sdom_tree, block_to_index, dom_tree, root);
        sdom_tree
    }

    fn compute_reduced_reachability(reduced_successors: &[BitSet]) -> Vec<BitSet> {
        let n = reduced_successors.len();
        let mut res = vec![BitSet::default(); n];

        // `reduced_successors` is in RPO and excludes back edges,
        // so visiting from the back lets us reuse already-computed successor sets.
        for node in (0..n).rev() {
            let mut reach = bitset_reduce(
                bitset_ops::Or,
                reduced_successors[node].iter().map(|succ| &res[succ]),
            )
            .map(Into::<BitSet>::into)
            .unwrap_or_default();
            // Definition 4 in the paper does not include the node itself.
            // But for Definition 5 (T_up) and subsequent computations to work
            // (for example when a back edge starts at `t` itself),
            // it's necessary to consider the node as reduced-reachable from itself.
            reach.insert(node);
            res[node] = reach;
        }

        res
    }

    fn compute_t_up_sets(
        reduced_reachability: &[BitSet],
        back_edges_by_source: &[Vec<usize>],
    ) -> Vec<BitSet> {
        // For every node `t`:
        reduced_reachability
            .iter()
            .map(|r_t| {
                let mut t_up = BitSet::default();
                // For every node `r` that is reduced reachable from `t`:
                for r in r_t.iter() {
                    // For back-edges beginning in `r`, add their targets to `t_up`.
                    for back_edge_target in &back_edges_by_source[r] {
                        t_up.insert(*back_edge_target);
                    }
                }
                // Remove nodes from `t_up` that are directly reduced-reachable from `t`.
                (&t_up - r_t).into()
            })
            .collect()
    }

    fn compute_tq_sets(
        t_up_sets: &[BitSet],
        reduced_successors: &[BitSet],
        back_edges_by_source: &[Vec<usize>],
        back_edge_targets: &BitSet,
        dfs_preorder: &[usize],
        dfs_postorder: &[usize],
    ) -> Vec<BitSet> {
        let n = t_up_sets.len();
        let mut tq_sets = vec![BitSet::default(); n];
        let computed = &mut vec![false; n];

        // Phase 1 (paper Sec 5.2): compute Tv for back-edge targets in DFS preorder.
        // This is Equation 1 over GT restricted to back-edge targets.
        for &t in dfs_preorder
            .iter()
            .filter(|t| back_edge_targets.contains(**t))
        {
            // In DFS preorder, dependencies for targets are already available.
            let mut t_q = bitset_reduce(
                bitset_ops::Or,
                t_up_sets[t].iter().map(|t_up| &tq_sets[t_up]),
            )
            .map(Into::<BitSet>::into)
            .unwrap_or_default();
            // Equation 1: T_v = {v} U ...
            t_q.insert(t);
            tq_sets[t] = t_q;
            computed[t] = true;
        }

        // Phase 2 (paper Sec 5.2): compute Ts\{s} for each back-edge source s by
        // unioning Tv of direct back-edge targets of s.
        for &s in dfs_preorder
            .iter()
            .filter(|s| !back_edges_by_source[**s].is_empty())
        {
            let ts = bitset_reduce(
                bitset_ops::Or,
                std::iter::once(&tq_sets[s])
                    .chain(back_edges_by_source[s].iter().map(|t| &tq_sets[*t])),
            )
            .map(Into::<BitSet>::into)
            .unwrap_or_default();
            tq_sets[s] = ts;
            computed[s] = true;
        }

        // Phase 3 (paper Sec 5.2): propagate the phase-2 result through the reduced
        // graph in DFS postorder (same shape as reduced reachability precomputation).
        for &q in dfs_postorder.iter().filter(|q| !computed[**q]) {
            let tq = bitset_reduce(
                bitset_ops::Or,
                reduced_successors[q].iter().map(|succ| &tq_sets[succ]),
            )
            .map(Into::<BitSet>::into)
            .unwrap_or_default();
            tq_sets[q] = tq;
        }

        // Finalize: For each v, add v to Tv.
        for (v, tv) in tq_sets.iter_mut().enumerate() {
            tv.insert(v);
        }

        tq_sets
    }

    fn block_index(&self, block: Ptr<BasicBlock>) -> Option<usize> {
        self.block_to_index.get(&block).copied()
    }

    /// If all uses are "analysable", returns the blocks in self.region containing uses.
    /// Otherwise, returns `None`.
    fn use_blocks_in_region(&self, ctx: &Context, value: Value) -> Option<BitSet> {
        let mut use_blocks = BitSet::default();
        for r#use in value.uses(ctx) {
            let Some(user_block) = r#use.user_op.deref(ctx).get_parent_block() else {
                // We don't know where the user op is, hence unanalysable
                return None;
            };
            let Some(ancestor) = find_ancestor_block_in_region(ctx, user_block, self.region) else {
                // Use in a different region, hence unanalysable
                return None;
            };
            let Some(use_idx) = self.block_index(ancestor) else {
                // Use in a block not reachable from entry, we can ignore the use
                continue;
            };
            use_blocks.insert(use_idx);
        }
        Some(use_blocks)
    }
}

impl RegionLiveness for LivenessTq {
    fn precompute(
        ctx: &Context,
        region: Ptr<Region>,
        dom_tree: &DomTree<Ptr<Region>, Context>,
    ) -> Self {
        Self::new(ctx, region, dom_tree)
    }

    fn is_live_in_block(&self, ctx: &Context, value: Value, query_block: Ptr<BasicBlock>) -> bool {
        let def_block = value
            .get_defining_block(ctx)
            .expect("Value must have a defining block for liveness queries");

        assert!(
            query_block.deref(ctx).get_parent_region() == Some(self.region)
                && def_block.deref(ctx).get_parent_region() == Some(self.region),
            "Query block must be in the same region as the definition block for liveness queries"
        );

        let (Some(def_idx), Some(query_idx)) =
            (self.block_index(def_block), self.block_index(query_block))
        else {
            // Definition / Query block not found in the region's DFS traversal: not reachable.
            return false;
        };

        let Some(use_blocks) = self.use_blocks_in_region(ctx, value) else {
            // If there are unanalysable uses, conservatively assume the value is live-in.
            return true;
        };

        if !self.sdom_tree[def_idx].contains(query_idx) || use_blocks.is_empty() {
            // If there's no use, or the definition doesn't dominate the query block,
            // then the value isn't live.
            return false;
        }

        // T(q, a) = T(q) intersect strict dominators of def(a).
        let t_q_a = &self.tq_sets[query_idx] & &self.sdom_tree[def_idx];

        // Section 4.1
        if self.is_reducible {
            // Find the node in t_q_a that dominates all others (Lemma 3).
            let all_dominator = t_q_a
                .iter()
                .reduce(|dom1, dom2| {
                    if self.sdom_tree[dom1].contains(dom2) {
                        dom1
                    } else {
                        dom2
                    }
                })
                .expect("t_q_a cannot be empty since it contains at least the query block itself");
            return !(&self.reduced_reachability[all_dominator] & &use_blocks).is_empty();
        }

        // Check if any block in T(q, a) reduced reaches a use block.
        t_q_a
            .iter()
            .any(|t_idx| !(&self.reduced_reachability[t_idx] & &use_blocks).is_empty())
    }

    fn is_live_out_block(&self, ctx: &Context, value: Value, query_block: Ptr<BasicBlock>) -> bool {
        let def_block = value
            .get_defining_block(ctx)
            .expect("Value must have a defining block for liveness queries");

        assert!(
            query_block.deref(ctx).get_parent_region() == Some(self.region)
                && def_block.deref(ctx).get_parent_region() == Some(self.region),
            "Query block must be in the same region as the definition block for liveness queries"
        );

        let (Some(def_idx), Some(query_idx)) =
            (self.block_index(def_block), self.block_index(query_block))
        else {
            // Definition / Query block not found in the region's DFS traversal: not reachable.
            return false;
        };

        let Some(use_blocks) = self.use_blocks_in_region(ctx, value) else {
            // If there are unanalysable uses, conservatively assume the value is live-out.
            return true;
        };

        // If we're querying for live-out at the definition block,
        // the variable is live-out IFF there is least one use in a different block.
        if def_block == query_block {
            return use_blocks.iter().any(|u_idx| u_idx != query_idx);
        }

        if !self.sdom_tree[def_idx].contains(query_idx) || use_blocks.is_empty() {
            // If there's no use, or the definition doesn't dominate the query block,
            // then the value isn't live.
            return false;
        }

        // T(q, a) = T(q) intersect strict dominators of def(a).
        let mut t_q_a: BitSet = (&self.tq_sets[query_idx] & &self.sdom_tree[def_idx]).into();

        // If q is in t_q_a and q is not a back-edge target. This is a special case inside the loop
        // in the paper which we've moved outside for efficiency.
        if t_q_a.contains(query_idx) && !self.back_edge_targets.contains(query_idx) {
            let uses_m_a: BitSet =
                (&use_blocks - &[query_idx].into_iter().collect::<BitSet>()).into();
            if !(&self.reduced_reachability[query_idx] & &uses_m_a).is_empty() {
                return true;
            }
            t_q_a.remove(query_idx);
        }

        // Check if any block in T(q, a) reduced reaches a use block.
        t_q_a
            .iter()
            .any(|t_idx| !(&self.reduced_reachability[t_idx] & &use_blocks).is_empty())
    }
}

/// Answer liveness queries for values in a region.
pub trait RegionLiveness {
    /// Precompute information for `region` and return query interface.
    fn precompute(
        ctx: &Context,
        region: Ptr<Region>,
        dom_tree: &DomTree<Ptr<Region>, Context>,
    ) -> Self;

    /// Is `value` live-in at the start of `query_block`?
    /// `value`'s definition block and `query_block` must both be in `Self`'s region.
    /// May conservatively return "live" for [Value]s with uses outside the region.
    fn is_live_in_block(&self, ctx: &Context, value: Value, query_block: Ptr<BasicBlock>) -> bool;

    /// Is `value` live-out at the end of `query_block`?
    /// `value`'s definition block and `query_block` must both be in `Self`'s region.
    /// May conservatively return "live" for [Value]s with uses outside the region.
    fn is_live_out_block(&self, ctx: &Context, value: Value, query_block: Ptr<BasicBlock>) -> bool;
}

/// Fast answers liveness queries, caching liveness pre-computation for regions.
pub struct Liveness<T: RegionLiveness> {
    regions: FxHashMap<Ptr<Region>, T>,
    dom_info: DomInfo,
}

impl<T: RegionLiveness> Default for Liveness<T> {
    fn default() -> Self {
        Self {
            regions: FxHashMap::default(),
            dom_info: DomInfo::default(),
        }
    }
}

impl<T: RegionLiveness> Liveness<T> {
    fn get_region_info(&mut self, ctx: &Context, region: Ptr<Region>) -> &T {
        let dom_tree = self.dom_info.get_dom_tree(ctx, region);
        self.regions
            .entry(region)
            .or_insert_with(|| T::precompute(ctx, region, dom_tree))
    }

    fn has_local_use_after_point(ctx: &Context, value: Value, point: OpInsertionPoint) -> bool {
        let mut op_iter = match point {
            OpInsertionPoint::BeforeOperation(op) => Some(op),
            OpInsertionPoint::AfterOperation(op) => op.deref(ctx).get_next(),
            OpInsertionPoint::AtBlockStart(block) => block.deref(ctx).get_head(),
            OpInsertionPoint::AtBlockEnd(_block) => None,
            OpInsertionPoint::Unset => panic!("Insertion point must be set for local use check"),
        };

        while let Some(op) = op_iter {
            let op = op.deref(ctx);
            if op.operands().any(|operand| operand == value) {
                return true;
            }
            op_iter = op.get_next();
        }
        false
    }

    /// Is `value` live-in at the start of `query_block`?
    pub fn is_live_in_block(
        &mut self,
        ctx: &Context,
        value: Value,
        query_block: Ptr<BasicBlock>,
    ) -> bool {
        let Some(def_block) = value.get_defining_block(ctx) else {
            return false;
        };
        let Some(def_region) = def_block.deref(ctx).get_parent_region() else {
            return false;
        };
        let Some(query_in_def_region) = find_ancestor_block_in_region(ctx, query_block, def_region)
        else {
            return false;
        };

        let info = self.get_region_info(ctx, def_region);
        info.is_live_in_block(ctx, value, query_in_def_region)
    }

    /// Is `value` live-out at the end of `query_block`?
    pub fn is_live_out_block(
        &mut self,
        ctx: &Context,
        value: Value,
        query_block: Ptr<BasicBlock>,
    ) -> bool {
        let Some(def_block) = value.get_defining_block(ctx) else {
            return false;
        };
        let Some(def_region) = def_block.deref(ctx).get_parent_region() else {
            return false;
        };
        let Some(query_in_def_region) = find_ancestor_block_in_region(ctx, query_block, def_region)
        else {
            return false;
        };

        let info = self.get_region_info(ctx, def_region);
        info.is_live_out_block(ctx, value, query_in_def_region)
    }

    /// Is `value` live at an operation insertion point?
    pub fn is_live_at_op_insertion_point(
        &mut self,
        ctx: &Context,
        value: Value,
        point: OpInsertionPoint,
    ) -> bool {
        let query_block = point.get_insertion_block(ctx).expect("point not set");

        match point {
            OpInsertionPoint::Unset => panic!("Insertion point must be set for liveness query"),
            OpInsertionPoint::AtBlockStart(query_block) => {
                self.is_live_in_block(ctx, value, query_block)
            }
            OpInsertionPoint::AtBlockEnd(query_block) => {
                self.is_live_out_block(ctx, value, query_block)
            }
            OpInsertionPoint::BeforeOperation(op) => {
                if !self.dom_info.value_strictly_dominates_op(ctx, value, op) {
                    // If the value doesn't dominate the operation, it can't be live before it
                    return false;
                }
                if Self::has_local_use_after_point(ctx, value, point) {
                    return true;
                }
                self.is_live_out_block(ctx, value, query_block)
            }
            OpInsertionPoint::AfterOperation(op) => {
                // Since the query is for liveness **after** this operation,
                // if **this** operation is defining the value, then it automatically
                // dominates the next operation (i.e., OpInsertionPoint::AfterOperation(op)).
                // Without this extra check, `value_strictly_dominates_op` would return false
                // and we would end up incorrectly reporting that the value is not live after.
                if let Value::OpResult {
                    op: value_def_op, ..
                } = value
                    && value_def_op != op
                    && !self.dom_info.value_strictly_dominates_op(ctx, value, op)
                {
                    // If the value doesn't dominate the operation, it can't be live after it
                    return false;
                }
                if Self::has_local_use_after_point(ctx, value, point) {
                    return true;
                }
                self.is_live_out_block(ctx, value, query_block)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Liveness;
    use crate::{
        analyses::fast_ssa_liveness::LivenessTq,
        basic_block::BasicBlock,
        builtin::{
            op_interfaces::{
                IsTerminatorInterface, OneRegionInterface, SingleBlockRegionInterface,
            },
            ops::{FuncOp, ModuleOp},
            types::{FunctionType, IntegerType, Signedness},
        },
        context::{Context, Ptr},
        derive::pliron_op,
        irbuild::inserter::OpInsertionPoint,
        op::Op,
        operation::Operation,
        value::Value,
    };

    #[pliron_op(name = "test.liveness.node", format, verifier = "succ")]
    struct NodeOp;

    #[pliron_op(
        name = "test.liveness.br",
        format,
        interfaces = [IsTerminatorInterface],
        verifier = "succ",
    )]
    struct BrOp;

    fn new_test_func(ctx: &mut Context, name: &str) -> (FuncOp, Ptr<BasicBlock>) {
        let module = ModuleOp::new(ctx, "test_liveness_mod".try_into().unwrap());
        let func_ty = FunctionType::get(ctx, vec![], vec![]);
        let func = FuncOp::new(ctx, name.try_into().unwrap(), func_ty);
        module.append_operation(ctx, func.get_operation(), 0);
        (func, func.get_entry_block(ctx))
    }

    fn append_block(ctx: &mut Context, func: &FuncOp) -> Ptr<BasicBlock> {
        let block = BasicBlock::new(ctx, None, vec![]);
        block.insert_at_back(func.get_region(ctx), ctx);
        block
    }

    fn insert_def(ctx: &mut Context, block: Ptr<BasicBlock>) -> (Ptr<Operation>, Value) {
        let i64_ty = IntegerType::get(ctx, 64, Signedness::Signed);
        let def_op = Operation::new(
            ctx,
            NodeOp::get_concrete_op_info(),
            vec![i64_ty.into()],
            vec![],
            vec![],
            0,
        );
        def_op.insert_at_back(block, ctx);
        let value = def_op.deref(ctx).get_result(0);
        (def_op, value)
    }

    fn insert_use(ctx: &mut Context, block: Ptr<BasicBlock>, value: Value) -> Ptr<Operation> {
        let use_op = Operation::new(
            ctx,
            NodeOp::get_concrete_op_info(),
            vec![],
            vec![value],
            vec![],
            0,
        );
        use_op.insert_at_back(block, ctx);
        use_op
    }

    fn insert_br(ctx: &mut Context, block: Ptr<BasicBlock>, succs: Vec<Ptr<BasicBlock>>) {
        let br_op = Operation::new(ctx, BrOp::get_concrete_op_info(), vec![], vec![], succs, 0);
        br_op.insert_at_back(block, ctx);
    }

    #[test]
    fn liveness_reducible_loop_blocks() {
        // CFG:
        // entry -> header
        // header -> body, exit
        // body -> header
        let ctx = &mut Context::new();
        let (func, entry) = new_test_func(ctx, "reducible_loop");
        let header = append_block(ctx, &func);
        let body = append_block(ctx, &func);
        let exit = append_block(ctx, &func);

        let (_def_op, val) = insert_def(ctx, entry);
        insert_use(ctx, body, val);

        insert_br(ctx, entry, vec![header]);
        insert_br(ctx, header, vec![body, exit]);
        insert_br(ctx, body, vec![header]);

        let mut liveness = Liveness::<LivenessTq>::default();
        assert!(liveness.is_live_in_block(ctx, val, header));
        assert!(liveness.is_live_out_block(ctx, val, header));
        assert!(!liveness.is_live_in_block(ctx, val, exit));
    }

    #[test]
    fn liveness_insertion_points_and_def_block_live_out() {
        // Single block with local use only.
        let ctx = &mut Context::new();
        let (_func, entry) = new_test_func(ctx, "single_block_local_use");

        let (def_op, val) = insert_def(ctx, entry);
        let use_op = insert_use(ctx, entry, val);

        let mut liveness = Liveness::<LivenessTq>::default();

        // Special-case in Algorithm 2: live-out at def block only if used outside def block.
        assert!(!liveness.is_live_out_block(ctx, val, entry));

        // Before defining op is never live; after defining op it is live because of local use.
        assert!(!liveness.is_live_at_op_insertion_point(
            ctx,
            val,
            OpInsertionPoint::BeforeOperation(def_op),
        ));
        assert!(liveness.is_live_at_op_insertion_point(
            ctx,
            val,
            OpInsertionPoint::AfterOperation(def_op),
        ));

        // Before use in same block, the value should be live.
        assert!(liveness.is_live_at_op_insertion_point(
            ctx,
            val,
            OpInsertionPoint::BeforeOperation(use_op),
        ));
    }

    #[test]
    fn liveness_irreducible_cfg_corner_case() {
        // Irreducible shape (multi-entry SCC {a, c}):
        // entry -> a, b
        // a -> c
        // b -> c
        // c -> a, exit
        let ctx = &mut Context::new();
        let (func, entry) = new_test_func(ctx, "irreducible");
        let a = append_block(ctx, &func);
        let b = append_block(ctx, &func);
        let c = append_block(ctx, &func);
        let exit = append_block(ctx, &func);

        let (_def_op, val) = insert_def(ctx, entry);
        insert_use(ctx, c, val);

        insert_br(ctx, entry, vec![a, b]);
        insert_br(ctx, a, vec![c]);
        insert_br(ctx, b, vec![c]);
        insert_br(ctx, c, vec![a, exit]);

        let mut liveness = Liveness::<LivenessTq>::default();

        // Dominated by entry and reaches use through irreducible SCC.
        assert!(liveness.is_live_in_block(ctx, val, b));
        assert!(liveness.is_live_out_block(ctx, val, b));

        // Use is not reachable from exit.
        assert!(!liveness.is_live_in_block(ctx, val, exit));
    }

    #[test]
    fn liveness_self_loop_is_reducible() {
        // CFG with a self-loop on `header` (header -> header back edge).
        // This is reducible (target dominates source reflexively).
        // entry -> header -> exit
        //          header -> header  (self-loop)
        let ctx = &mut Context::new();
        let (func, entry) = new_test_func(ctx, "self_loop");
        let header = append_block(ctx, &func);
        let exit = append_block(ctx, &func);

        let (_def_op, val) = insert_def(ctx, entry);
        insert_use(ctx, header, val);

        insert_br(ctx, entry, vec![header]);
        insert_br(ctx, header, vec![header, exit]);

        let mut liveness = Liveness::<LivenessTq>::default();

        // val is defined in entry and used in header, so it is live-in at header.
        assert!(liveness.is_live_in_block(ctx, val, header));
        // Not live past header (no use in exit).
        assert!(!liveness.is_live_in_block(ctx, val, exit));

        // Verify the CFG was treated as reducible (fast path exercised).
        let def_region = entry.deref(ctx).get_parent_region().unwrap();
        let info = liveness.get_region_info(ctx, def_region);
        assert!(
            info.is_reducible,
            "Self-loop CFG must be classified as reducible"
        );
    }

    #[test]
    fn liveness_dead_value_no_uses() {
        // Val is defined but never used. All liveness queries must return false,
        // exercising the `use_blocks.is_empty()` early-exit path in the algorithms.
        // CFG: entry -> successor (so entry sdom-dominates successor)
        let ctx = &mut Context::new();
        let (func, entry) = new_test_func(ctx, "dead_value");
        let successor = append_block(ctx, &func);

        let (_def_op, val) = insert_def(ctx, entry);
        // No uses of `val`.

        insert_br(ctx, entry, vec![successor]);

        let mut liveness = Liveness::<LivenessTq>::default();
        // query block is dominated by def block — exercises use_blocks.is_empty() path.
        assert!(!liveness.is_live_in_block(ctx, val, successor));
        // def == query block, no uses anywhere.
        assert!(!liveness.is_live_out_block(ctx, val, entry));
    }

    #[test]
    fn liveness_def_not_dominating_query_diamond() {
        // Diamond CFG: entry -> {left, right} -> merge.
        // Val is defined and used locally in `left`. Querying liveness at `right` and `entry`
        // (neither of which is dominated by `left`) exercises the
        // `!sdom_tree[def_idx].contains(query_idx)` early-exit path.
        let ctx = &mut Context::new();
        let (func, entry) = new_test_func(ctx, "diamond");
        let left = append_block(ctx, &func);
        let right = append_block(ctx, &func);
        let merge = append_block(ctx, &func);

        let (_def_op, val) = insert_def(ctx, left);
        // Local use in `left` — SSA dominance is satisfied (def dominates its own block).
        insert_use(ctx, left, val);

        insert_br(ctx, entry, vec![left, right]);
        insert_br(ctx, left, vec![merge]);
        insert_br(ctx, right, vec![merge]);

        let mut liveness = Liveness::<LivenessTq>::default();
        // `left` does not dominate `right` — early exit fires, must be false.
        assert!(!liveness.is_live_in_block(ctx, val, right));
        assert!(!liveness.is_live_out_block(ctx, val, right));
        // `left` does not dominate `entry` — early exit fires, must be false.
        assert!(!liveness.is_live_in_block(ctx, val, entry));
        // Local use only in `left`, not live-out past `left`.
        assert!(!liveness.is_live_out_block(ctx, val, left));
    }

    #[test]
    fn liveness_live_out_false_when_only_use_at_query_block() {
        // CFG: entry -> a -> exit.
        // Val is defined in `entry` and used only in `a`.
        // is_live_out_block(val, a) must be false: exercises the branch where q ∈ T(q,a)
        // but q is NOT a back-edge target, so uses at q are stripped, leaving no reachable use.
        let ctx = &mut Context::new();
        let (func, entry) = new_test_func(ctx, "use_at_query_only");
        let a = append_block(ctx, &func);
        let exit = append_block(ctx, &func);

        let (_def_op, val) = insert_def(ctx, entry);
        insert_use(ctx, a, val);

        insert_br(ctx, entry, vec![a]);
        insert_br(ctx, a, vec![exit]);

        let mut liveness = Liveness::<LivenessTq>::default();
        assert!(liveness.is_live_in_block(ctx, val, a));
        // Only use is in `a` itself — not live-out past the end of `a`.
        assert!(!liveness.is_live_out_block(ctx, val, a));
        // Also live-out at entry since `a` (a different block) uses it.
        assert!(liveness.is_live_out_block(ctx, val, entry));
    }

    #[test]
    fn liveness_loop_use_in_header_back_edge_target() {
        // CFG: entry -> header -> {body, exit}; body -> header.
        // Val is defined in `entry` and used in `header` (the loop header, which is a back-edge
        // target). This exercises the is_live_out_block path where q IS a back-edge target so
        // uses at q are NOT stripped — the only use is at the query block, but since q is a
        // loop header there is a non-trivial path from q back to itself, making val live-out.
        let ctx = &mut Context::new();
        let (func, entry) = new_test_func(ctx, "loop_header_use");
        let header = append_block(ctx, &func);
        let body = append_block(ctx, &func);
        let exit = append_block(ctx, &func);

        let (_def_op, val) = insert_def(ctx, entry);
        // Use is in `header` only (the back-edge target).
        insert_use(ctx, header, val);

        insert_br(ctx, entry, vec![header]);
        insert_br(ctx, header, vec![body, exit]);
        insert_br(ctx, body, vec![header]);

        let mut liveness = Liveness::<LivenessTq>::default();
        assert!(liveness.is_live_in_block(ctx, val, header));
        // val is live-in at body because body -> header and header uses val.
        assert!(liveness.is_live_in_block(ctx, val, body));
        // header is a back-edge target: live-out because the loop can re-execute header.
        assert!(liveness.is_live_out_block(ctx, val, header));
        // val is NOT live-in at exit since there's no use reachable from exit.
        assert!(!liveness.is_live_in_block(ctx, val, exit));
    }
}
