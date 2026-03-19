//! Control-flow-graph traversals

use super::ControlFlowGraph;
use rustc_hash::FxHashSet;

/// Region traversal utilities
pub mod region {
    use super::*;

    fn post_order_walk_component<G, GraphContext>(
        ctx: &GraphContext,
        graph: &G,
        node: G::Node,
        seen_nodes: &mut FxHashSet<G::Node>,
        po: &mut Vec<G::Node>,
    ) where
        G: ControlFlowGraph<GraphContext>,
    {
        if seen_nodes.contains(&node) {
            // node already visited.
            return;
        }
        seen_nodes.insert(node.clone());

        // Visit successors before visiting this node.
        for succ in graph.successors(ctx, &node) {
            post_order_walk_component(ctx, graph, succ, seen_nodes, po);
        }
        // Visit this node.
        po.push(node);
    }

    /// Compute post-order of the nodes in a graph.
    pub fn post_order<G, GraphContext>(ctx: &GraphContext, graph: &G) -> Vec<G::Node>
    where
        G: ControlFlowGraph<GraphContext>,
    {
        post_order_by_component(ctx, graph)
            .into_iter()
            .flatten()
            .collect::<Vec<G::Node>>()
    }

    /// Compute the post-order of the nodes in a graph,
    /// providing result for each connected component separately.
    pub fn post_order_by_component<G, GraphContext>(
        ctx: &GraphContext,
        graph: &G,
    ) -> Vec<Vec<G::Node>>
    where
        G: ControlFlowGraph<GraphContext>,
    {
        let seen_nodes = &mut FxHashSet::<G::Node>::default();
        let mut po_by_component = Vec::<Vec<G::Node>>::new();

        // Walk every node (not just entry) since we may have unreachable nodes.
        for node in graph.nodes(ctx) {
            let mut po = Vec::<G::Node>::new();
            post_order_walk_component(ctx, graph, node, seen_nodes, &mut po);
            if !po.is_empty() {
                po_by_component.push(po);
            }
        }
        po_by_component
    }

    /// Compute reverse-post-order of the nodes in a graph.
    pub fn topological_order<G, GraphContext>(ctx: &GraphContext, graph: &G) -> Vec<G::Node>
    where
        G: ControlFlowGraph<GraphContext>,
    {
        topological_order_by_component(ctx, graph)
            .into_iter()
            .flatten()
            .collect::<Vec<G::Node>>()
    }

    /// Compute the reverse-post-order of the nodes in a graph,
    /// providing result for each connected component separately.
    /// Note: Component wise order remains the same as the input.
    pub fn topological_order_by_component<G, GraphContext>(
        ctx: &GraphContext,
        graph: &G,
    ) -> Vec<Vec<G::Node>>
    where
        G: ControlFlowGraph<GraphContext>,
    {
        let seen_nodes = &mut FxHashSet::<G::Node>::default();
        let mut rpo_by_component = Vec::<Vec<G::Node>>::new();

        // Walk every node (not just entry) since we may have unreachable nodes.
        for node in graph.nodes(ctx) {
            let mut po = Vec::<G::Node>::new();
            post_order_walk_component(ctx, graph, node, seen_nodes, &mut po);
            if !po.is_empty() {
                rpo_by_component.push(po.into_iter().rev().collect());
            }
        }
        rpo_by_component
    }
}

#[cfg(test)]
mod tests {
    use super::region::{post_order, topological_order};
    use crate::graph::ControlFlowGraph;

    #[derive(Clone, Debug)]
    struct Node {
        data: u32,
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
            (!ctx.is_empty()).then_some(0)
        }

        fn nodes<'a>(&'a self, ctx: &'a Vec<Node>) -> Box<dyn Iterator<Item = Self::Node> + 'a> {
            Box::new(0..ctx.len())
        }
    }

    fn n(data: u32, succs: &[usize]) -> Node {
        Node {
            data,
            succs: succs.to_vec(),
        }
    }

    fn data_order(ctx: &[Node], order: &[usize]) -> Vec<u32> {
        order.iter().map(|&idx| ctx[idx].data).collect()
    }

    fn assert_is_permutation_of_all_nodes(ctx: &[Node], order: &[usize]) {
        assert_eq!(order.len(), ctx.len());
        let mut seen = vec![false; ctx.len()];
        for &idx in order {
            assert!(idx < ctx.len(), "index {idx} out of bounds");
            assert!(!seen[idx], "duplicate node index {idx}");
            seen[idx] = true;
        }
        assert!(seen.into_iter().all(|v| v));
    }

    fn assert_post_order_edge_property_for_dag(ctx: &[Node], po: &[usize]) {
        let mut pos = vec![usize::MAX; ctx.len()];
        for (i, &idx) in po.iter().enumerate() {
            pos[idx] = i;
        }
        for (u, node) in ctx.iter().enumerate() {
            for &v in &node.succs {
                assert!(
                    pos[v] < pos[u],
                    "expected successor {v} to appear before predecessor {u} in post-order"
                );
            }
        }
    }

    fn assert_topological_edge_property_for_dag(ctx: &[Node], rpo: &[usize]) {
        let mut pos = vec![usize::MAX; ctx.len()];
        for (i, &idx) in rpo.iter().enumerate() {
            pos[idx] = i;
        }
        for (u, node) in ctx.iter().enumerate() {
            for &v in &node.succs {
                assert!(
                    pos[u] < pos[v],
                    "expected predecessor {u} to appear before successor {v} in reverse post-order"
                );
            }
        }
    }

    #[test]
    fn post_order_linear_chain() {
        let ctx = vec![n(10, &[1]), n(20, &[2]), n(30, &[])];

        let po = post_order(&ctx, &ArenaGraph);
        let rpo = topological_order(&ctx, &ArenaGraph);

        assert_eq!(data_order(&ctx, &po), vec![30, 20, 10]);
        assert_eq!(data_order(&ctx, &rpo), vec![10, 20, 30]);
        assert_is_permutation_of_all_nodes(&ctx, &po);
        assert_post_order_edge_property_for_dag(&ctx, &po);
        assert_topological_edge_property_for_dag(&ctx, &rpo);
    }

    #[test]
    fn post_order_diamond_dag() {
        let ctx = vec![n(0, &[1, 2]), n(1, &[3]), n(2, &[3]), n(3, &[])];

        let po = post_order(&ctx, &ArenaGraph);
        let rpo = topological_order(&ctx, &ArenaGraph);

        assert_eq!(data_order(&ctx, &po), vec![3, 1, 2, 0]);
        assert_eq!(data_order(&ctx, &rpo), vec![0, 2, 1, 3]);
        assert_is_permutation_of_all_nodes(&ctx, &po);
        assert_post_order_edge_property_for_dag(&ctx, &po);
        assert_topological_edge_property_for_dag(&ctx, &rpo);
    }

    #[test]
    fn post_order_handles_cycle_and_isolated_node() {
        let ctx = vec![n(0, &[1]), n(1, &[2]), n(2, &[0]), n(99, &[])];

        let po = post_order(&ctx, &ArenaGraph);
        let rpo = topological_order(&ctx, &ArenaGraph);

        assert_eq!(data_order(&ctx, &po), vec![2, 1, 0, 99]);
        assert_eq!(data_order(&ctx, &rpo), vec![0, 1, 2, 99]);
        assert_is_permutation_of_all_nodes(&ctx, &po);
    }

    #[test]
    fn post_order_covers_disconnected_components() {
        let ctx = vec![n(0, &[1]), n(1, &[]), n(2, &[3]), n(3, &[]), n(4, &[])];

        let po = post_order(&ctx, &ArenaGraph);
        let rpo = topological_order(&ctx, &ArenaGraph);

        assert_eq!(data_order(&ctx, &po), vec![1, 0, 3, 2, 4]);
        assert_eq!(data_order(&ctx, &rpo), vec![0, 1, 2, 3, 4]);
        assert_is_permutation_of_all_nodes(&ctx, &po);
        assert_post_order_edge_property_for_dag(&ctx, &po);
        assert_topological_edge_property_for_dag(&ctx, &rpo);
    }
}
