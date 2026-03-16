//! IR and control-flow-graph utilities

pub mod traversals;
pub mod visualize;
pub mod walkers;

use crate::{
    basic_block::BasicBlock,
    context::{Context, Ptr},
    linked_list::ContainsLinkedList,
    region::Region,
};
use std::hash::Hash;

pub trait ControlFlowGraph<GraphContext> {
    type Node: Eq + Hash + Clone;

    /// Returns the successors of a node in the graph.
    fn successors(&self, ctx: &GraphContext, node: &Self::Node) -> Vec<Self::Node>;

    /// Returns the predecessors of a node in the graph.
    fn predecessors(&self, ctx: &GraphContext, node: &Self::Node) -> Vec<Self::Node>;

    /// Returns the entry node of the graph.
    fn entry_node(&self, ctx: &GraphContext) -> Option<Self::Node>;

    /// Get all nodes in the graph.
    fn nodes<'a>(&'a self, ctx: &'a GraphContext) -> Box<dyn Iterator<Item = Self::Node> + 'a>;
}

impl ControlFlowGraph<Context> for Ptr<Region> {
    type Node = Ptr<BasicBlock>;

    fn successors(&self, ctx: &Context, node: &Self::Node) -> Vec<Self::Node> {
        node.deref(ctx).succs(ctx)
    }

    fn predecessors(&self, ctx: &Context, node: &Self::Node) -> Vec<Self::Node> {
        node.preds(ctx)
    }

    fn entry_node(&self, ctx: &Context) -> Option<Self::Node> {
        self.deref(ctx).get_head()
    }

    fn nodes<'a>(&'a self, ctx: &'a Context) -> Box<dyn Iterator<Item = Self::Node> + 'a> {
        Box::new(self.deref(ctx).iter(ctx))
    }
}
