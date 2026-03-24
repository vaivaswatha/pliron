use rustc_hash::{FxHashMap, FxHashSet};

use crate::graph::{ControlFlowGraph, traversals};

/// A node in the dominator tree.
struct DomTreeNode<G, GraphContext>
where
    G: ControlFlowGraph<GraphContext>,
{
    /// The immediate dominator of self.
    parent: Option<G::Node>,
    /// The nodes that self immediately dominates.
    children: Vec<G::Node>,
}

/// Represents dominator tree for a control-flow-graph
pub struct DomTree<G, GraphContext>(FxHashMap<G::Node, DomTreeNode<G, GraphContext>>)
where
    G: ControlFlowGraph<GraphContext>;

/// Maps each node to its dominance frontier
pub struct DomFrontierMap<G, GraphContext>(FxHashMap<G::Node, FxHashSet<G::Node>>)
where
    G: ControlFlowGraph<GraphContext>;

/// Computes a dominator tree for `graph`.
/// Only considers nodes reachable from the entry node of the graph.
// An implementation of the algorithm from page 7 of
// "A Simple, Fast Dominance Algorithm" by Cooper et. al.
pub fn compute_dominator_tree<G, GraphContext>(
    ctx: &GraphContext,
    graph: &G,
) -> DomTree<G, GraphContext>
where
    G: ControlFlowGraph<GraphContext>,
{
    let Some(entry_node) = graph.entry_node(ctx) else {
        return DomTree(FxHashMap::default());
    };

    // We consider only the first connected component for the dominator tree,
    // since the entry node is guaranteed to be in the first component,
    // and all nodes not reachable from the entry node are not dominated by the entry.
    // (i.e. they are roots of their own dominator trees - which we don't care about).
    let rpo = traversals::region::topological_order_by_component(ctx, graph)
        .into_iter()
        .next()
        .expect("Graph has no components, but has an entry node");

    let rpo_index: FxHashMap<G::Node, usize> = rpo
        .iter()
        .enumerate()
        .map(|(i, node)| (node.clone(), i))
        .collect();

    let mut dom: Vec<Option<usize>> = vec![None; rpo.len()];
    assert!(
        rpo_index[&entry_node] == 0,
        "Entry node is not the first block in our CFG"
    );
    dom[0] = Some(0);

    fn intersect(mut finger1: usize, mut finger2: usize, dom: &[Option<usize>]) -> usize {
        while finger1 != finger2 {
            while finger1 > finger2 {
                finger1 = dom[finger1].unwrap();
            }
            while finger2 > finger1 {
                finger2 = dom[finger2].unwrap();
            }
        }
        finger1
    }

    let mut changed = true;
    while changed {
        changed = false;

        for (i, node) in rpo.iter().enumerate().skip(1) {
            let preds = graph.predecessors(ctx, node);
            // only consider predecessors reachable from entry (exactly the predecessors in rpo_index)
            let reachable_preds = preds.iter().filter(|p| rpo_index.contains_key(p));

            // new_idom <- first (processed) predecessor of b (pick one)
            let picked_pred = reachable_preds
                .clone()
                .find(|p| dom[rpo_index[p]].is_some())
                .unwrap();
            let mut new_idom = rpo_index[picked_pred];

            // for all other (reachable) predecessors, p, of b:
            for pred in reachable_preds.filter(|p| *p != picked_pred) {
                let pred_idx = rpo_index[pred];
                match dom[pred_idx] {
                    None => {}
                    Some(_) => {
                        new_idom = intersect(pred_idx, new_idom, &dom);
                    }
                }
            }

            if dom[i] != Some(new_idom) {
                dom[i] = Some(new_idom);
                changed = true;
            }
        }
    }

    let mut dom_tree = DomTree(FxHashMap::default());
    let entry = DomTreeNode {
        parent: None,
        children: vec![],
    };
    dom_tree.0.insert(rpo[0].clone(), entry);

    let child_parent = dom
        .iter()
        .enumerate()
        .skip(1)
        .map(|(i, parent)| (rpo[i].clone(), rpo[parent.unwrap()].clone()));

    for (child_node, parent_node) in child_parent {
        let child_dom_node = DomTreeNode {
            parent: Some(parent_node.clone()),
            children: vec![],
        };
        dom_tree.0.insert(child_node.clone(), child_dom_node);
        let parent_dom_node = dom_tree.0.get_mut(&parent_node).unwrap();
        parent_dom_node.children.push(child_node.clone())
    }

    dom_tree
}

impl<G, GraphContext> DomTree<G, GraphContext>
where
    G: ControlFlowGraph<GraphContext>,
{
    /// Does `dominator` dominate `dominatee`?
    pub fn dominates(&self, dominator: &G::Node, dominatee: &G::Node) -> bool {
        let mut node_opt = Some(dominatee.clone());
        while let Some(node) = node_opt {
            if node == *dominator {
                return true;
            }
            node_opt = self.0[&node].parent.clone();
        }
        false
    }

    /// Does the dominator tree contain `node`?
    /// That is, is `node` reachable from the entry node?
    pub fn contains(&self, node: &G::Node) -> bool {
        self.0.contains_key(node)
    }

    /// Return the immediate dominator of `node`
    pub fn idom(&self, node: &G::Node) -> Option<G::Node> {
        self.0[node].parent.clone()
    }

    /// Return an iterator over the dominators of `node`, starting with `node` itself,
    /// then its immediate dominator, and so on up to the root.
    pub fn dominators(&self, node: &G::Node) -> impl Iterator<Item = G::Node> + '_ {
        std::iter::successors(Some(node.clone()), |n| self.0[n].parent.clone())
    }

    /// Get an iterator over the children nodes
    pub fn children(&self, node: &G::Node) -> impl Iterator<Item = G::Node> + '_ {
        self.0[node].children.iter().cloned()
    }
}

impl<G, GraphContext> DomFrontierMap<G, GraphContext>
where
    G: ControlFlowGraph<GraphContext>,
{
    /// Construct `graph`'s dominance frontier map, given that `dom_tree` is the dominance tree
    /// generated from `graph`
    // This method implements the algorithm from "A Simple, Fast Dominance Algorithm" by Cooper et. al.
    pub fn new(ctx: &GraphContext, graph: &G, dom_tree: &DomTree<G, GraphContext>) -> Self {
        let mut res: FxHashMap<G::Node, FxHashSet<G::Node>> = graph
            .nodes(ctx)
            .map(|n| (n, FxHashSet::default()))
            .collect();
        for b in graph.nodes(ctx) {
            let preds = graph.predecessors(ctx, &b);
            if preds.len() < 2 {
                continue;
            }
            let b_idom = dom_tree.idom(&b).unwrap();
            for p in preds.into_iter().filter(|n| dom_tree.contains(n)) {
                for runner in dom_tree.dominators(&p).take_while(|n| *n != b_idom) {
                    res.get_mut(&runner).unwrap().insert(b.clone());
                }
            }
        }
        DomFrontierMap(res)
    }

    /// Gets the set of all nodes in `n`'s dominance frontier
    pub fn frontier<'a>(&'a self, n: &G::Node) -> &'a FxHashSet<G::Node> {
        &self.0[n]
    }
}

#[cfg(test)]
mod tests {
    use super::{DomFrontierMap, compute_dominator_tree};
    use crate::graph::ControlFlowGraph;
    use rustc_hash::FxHashSet;
    use std::collections::HashSet;

    #[derive(Clone, Debug)]
    struct Node {
        succs: Vec<usize>,
    }

    #[derive(Clone, Copy, Debug)]
    struct ArenaGraph;

    impl ControlFlowGraph<Vec<Node>> for ArenaGraph {
        type Node = usize;

        fn successors(&self, ctx: &Vec<Node>, node: &Self::Node) -> Vec<Self::Node> {
            ctx[*node].succs.clone()
        }

        fn predecessors(&self, ctx: &Vec<Node>, node: &Self::Node) -> Vec<Self::Node> {
            ctx.iter()
                .enumerate()
                .filter_map(|(idx, n)| n.succs.contains(node).then_some(idx))
                .collect()
        }

        fn entry_node(&self, ctx: &Vec<Node>) -> Option<Self::Node> {
            if ctx.is_empty() { None } else { Some(0) }
        }

        fn nodes<'a>(&'a self, ctx: &'a Vec<Node>) -> Box<dyn Iterator<Item = Self::Node> + 'a> {
            Box::new(0..ctx.len())
        }
    }

    fn n(succs: &[usize]) -> Node {
        Node {
            succs: succs.to_vec(),
        }
    }

    #[test]
    fn dominator_tree_empty_graph() {
        let ctx: Vec<Node> = vec![];
        let dom = compute_dominator_tree(&ctx, &ArenaGraph);
        assert_eq!(dom.0.len(), 0);
    }

    #[test]
    fn dominator_tree_single_node() {
        let ctx = vec![n(&[])];
        let dom = compute_dominator_tree(&ctx, &ArenaGraph);
        assert_eq!(dom.0[&0].parent, None);
    }

    #[test]
    fn dominator_tree_linear_chain() {
        // 0 -> 1 -> 2
        let ctx = vec![
            /* 0 */ n(&[1]),
            /* 1 */ n(&[2]),
            /* 2 */ n(&[]),
        ];
        let dom = compute_dominator_tree(&ctx, &ArenaGraph);
        assert_eq!(dom.0.len(), 3);
        assert_eq!(dom.0[&0].parent, None);
        assert_eq!(dom.0[&1].parent, Some(0));
        assert_eq!(dom.0[&2].parent, Some(1));
    }

    #[test]
    fn dominator_tree_diamond() {
        //      0
        //     / \
        //    1   2
        //     \ /
        //      3
        let ctx = vec![
            /* 0 */ n(&[1, 2]),
            /* 1 */ n(&[3]),
            /* 2 */ n(&[3]),
            /* 3 */ n(&[]),
        ];
        let dom = compute_dominator_tree(&ctx, &ArenaGraph);
        assert_eq!(dom.0.len(), 4);
        assert_eq!(dom.0[&0].parent, None);
        assert_eq!(dom.0[&1].parent, Some(0));
        assert_eq!(dom.0[&2].parent, Some(0));
        assert_eq!(dom.0[&3].parent, Some(0));

        assert_eq!(dom.children(&0).collect::<HashSet<_>>(), [1, 2, 3].into());
    }

    #[test]
    fn dominator_tree_loop() {
        //            +--------+
        //            v        |
        //  0 -> 1 (header) -> 2 (body)
        //            |
        //            v
        //            3 (exit)
        let ctx = vec![
            /* 0 */ n(&[1]),
            /* 1 */ n(&[2, 3]),
            /* 2 */ n(&[1]),
            /* 3 */ n(&[]),
        ];
        let dom = compute_dominator_tree(&ctx, &ArenaGraph);
        assert_eq!(dom.0.len(), 4);
        assert_eq!(dom.0[&0].parent, None);
        assert_eq!(dom.0[&1].parent, Some(0));
        assert_eq!(dom.0[&2].parent, Some(1));
        assert_eq!(dom.0[&3].parent, Some(1));

        assert!(dom.dominates(&1, &3));
        assert!(!dom.dominates(&2, &3));

        assert_eq!(dom.children(&0).collect::<HashSet<_>>(), [1].into());
        assert_eq!(dom.children(&1).collect::<HashSet<_>>(), [2, 3].into());
        assert_eq!(dom.children(&2).collect::<HashSet<_>>(), [].into());
        assert_eq!(dom.children(&3).collect::<HashSet<_>>(), [].into());
    }

    #[test]
    fn dominator_tree_cooper_fig4() {
        // From "A Simple, Fast Dominance Algorithm" by Cooper et al.
        //
        //         0 (entry)
        //        / \
        //       v   v
        //      1     2
        //      |    / \
        //      v   v   v
        //      3 ⇄ 4 ⇄ 5
        let ctx = vec![
            /* 0 */ n(&[1, 2]),
            /* 1 */ n(&[3]),
            /* 2 */ n(&[4, 5]),
            /* 3 */ n(&[4]),
            /* 4 */ n(&[3, 5]),
            /* 5 */ n(&[4]),
        ];
        let dom = compute_dominator_tree(&ctx, &ArenaGraph);
        assert_eq!(dom.0.len(), 6);
        assert_eq!(dom.0[&0].parent, None);
        assert_eq!(dom.0[&1].parent, Some(0));
        assert_eq!(dom.0[&2].parent, Some(0));
        assert_eq!(dom.0[&3].parent, Some(0));
        assert_eq!(dom.0[&4].parent, Some(0));
        assert_eq!(dom.0[&5].parent, Some(0));

        assert!(dom.dominates(&0, &1));
        assert!(!dom.dominates(&2, &4));
    }

    #[test]
    fn dominator_tree_dragon() {
        // From the Dragon Book, second edition, pg 657
        let ctx = vec![
            /* 0 */ n(&[1, 2]),
            /* 1 */ n(&[2]),
            /* 2 */ n(&[3]),
            /* 3 */ n(&[4, 5, 2]),
            /* 4 */ n(&[6]),
            /* 5 */ n(&[6]),
            /* 6 */ n(&[3, 7]),
            /* 7 */ n(&[8, 9, 2]),
            /* 8 */ n(&[0]),
            /* 9 */ n(&[6]),
        ];
        let dom = compute_dominator_tree(&ctx, &ArenaGraph);
        assert_eq!(dom.0.len(), 10);
        assert_eq!(dom.0[&0].parent, None);
        assert_eq!(dom.0[&1].parent, Some(0));
        assert_eq!(dom.0[&2].parent, Some(0));
        assert_eq!(dom.0[&3].parent, Some(2));
        assert_eq!(dom.0[&4].parent, Some(3));
        assert_eq!(dom.0[&5].parent, Some(3));
        assert_eq!(dom.0[&6].parent, Some(3));
        assert_eq!(dom.0[&7].parent, Some(6));
        assert_eq!(dom.0[&8].parent, Some(7));
        assert_eq!(dom.0[&9].parent, Some(7));

        assert_eq!(dom.children(&3).collect::<HashSet<_>>(), [4, 5, 6].into());
    }

    #[test]
    fn dominator_tree_disconnected_components() {
        // 0 -> 1    2 -> 3
        let ctx = vec![
            /* 0 */ n(&[1]),
            /* 1 */ n(&[]),
            /* 2 */ n(&[3]),
            /* 3 */ n(&[]),
        ];
        let dom = compute_dominator_tree(&ctx, &ArenaGraph);
        assert_eq!(dom.0.len(), 2);
        assert_eq!(dom.0[&0].parent, None);
        assert_eq!(dom.0[&1].parent, Some(0));

        assert_eq!(dom.children(&0).collect::<HashSet<_>>(), [1].into());
    }

    #[test]
    fn dom_frontier_empty() {
        // test that we can construct a dominance frontier map from an empty graph without crashing
        let ctx: Vec<Node> = vec![];
        let dom = compute_dominator_tree(&ctx, &ArenaGraph);
        let _df = DomFrontierMap::new(&ctx, &ArenaGraph, &dom);
    }

    #[test]
    fn dom_frontier_single() {
        let ctx = vec![n(&[])];
        let dom = compute_dominator_tree(&ctx, &ArenaGraph);
        let df = DomFrontierMap::new(&ctx, &ArenaGraph, &dom);
        assert_eq!(*df.frontier(&0), FxHashSet::from_iter([]));
    }

    #[test]
    fn dom_frontier_diamond() {
        //      0
        //     / \
        //    1   2
        //     \ /
        //      3
        let ctx = vec![
            /* 0 */ n(&[1, 2]),
            /* 1 */ n(&[3]),
            /* 2 */ n(&[3]),
            /* 3 */ n(&[]),
        ];
        let dom = compute_dominator_tree(&ctx, &ArenaGraph);
        let df = DomFrontierMap::new(&ctx, &ArenaGraph, &dom);

        assert_eq!(*df.frontier(&0), FxHashSet::from_iter([]));
        assert_eq!(*df.frontier(&1), FxHashSet::from_iter([3]));
        assert_eq!(*df.frontier(&2), FxHashSet::from_iter([3]));
        assert_eq!(*df.frontier(&3), FxHashSet::from_iter([]));
    }

    #[test]
    fn dom_frontier_diamond_unreachable() {
        //      0      4     6    7
        //     / \     |          |
        //    1   2 <- 5          8
        //     \ /
        //      3
        let ctx = vec![
            /* 0 */ n(&[1, 2]),
            /* 1 */ n(&[3]),
            /* 2 */ n(&[3]),
            /* 3 */ n(&[]),
            /* 4 */ n(&[5]),
            /* 5 */ n(&[2]),
            /* 6 */ n(&[]),
            /* 7 */ n(&[8]),
            /* 8 */ n(&[]),
        ];
        let dom = compute_dominator_tree(&ctx, &ArenaGraph);
        let df = DomFrontierMap::new(&ctx, &ArenaGraph, &dom);

        assert_eq!(*df.frontier(&0), FxHashSet::from_iter([]));
        assert_eq!(*df.frontier(&1), FxHashSet::from_iter([3]));
        assert_eq!(*df.frontier(&2), FxHashSet::from_iter([3]));
        assert_eq!(*df.frontier(&3), FxHashSet::from_iter([]));
        assert_eq!(*df.frontier(&4), FxHashSet::from_iter([]));
        assert_eq!(*df.frontier(&5), FxHashSet::from_iter([]));
        assert_eq!(*df.frontier(&6), FxHashSet::from_iter([]));
        assert_eq!(*df.frontier(&7), FxHashSet::from_iter([]));
        assert_eq!(*df.frontier(&8), FxHashSet::from_iter([]));
    }

    #[test]
    fn dom_frontier_appel() {
        // Figure 19.5 from Andrew Appel's "Modern Compiler Implementation in ML"
        let ctx = vec![
            /* 0  */ n(&[1, 4, 8]),
            /* 1  */ n(&[2]),
            /* 2  */ n(&[2, 3]),
            /* 3  */ n(&[12]),
            /* 4  */ n(&[5, 6]),
            /* 5  */ n(&[3, 7]),
            /* 6  */ n(&[7, 11]),
            /* 7  */ n(&[4, 12]),
            /* 8  */ n(&[9, 10]),
            /* 9  */ n(&[11]),
            /* 10 */ n(&[11]),
            /* 11 */ n(&[12]),
            /* 12 */ n(&[]),
        ];
        let dom = compute_dominator_tree(&ctx, &ArenaGraph);
        let df = DomFrontierMap::new(&ctx, &ArenaGraph, &dom);
        assert_eq!(*df.frontier(&4), FxHashSet::from_iter([3, 4, 11, 12]));
    }
}
