//! Walk the IR graph. At each node:
//! - Call a callback to process the node.
//! - Walk over the children.
//! The relative orders of performing the above is configurable.
//! Throughout this module, only parent-child relations are considered,
//!   i.e., operations->regions, region->blocks and block->operations.
//!   Successor/predecessor relations b/w blocks (control-flow-graph) is out-of-scope.
//! Care must be taken if modifications are made to the graph during the walk.
//! Safe modifications:
//!    Node deletions: A node can be deleted from its parent only when the
//!        parent is visited in a PostOrder walk, after all children are processed.
//!        This ensure deleted nodes aren't visited.
//!    Node additions: A node can be inserted into its parent only when the
//!        parent is visited in a PreOrder walk, before any child is processed.
//!        This ensures that the new node gets visited.
//!    Other graph modifications such as changing the order b/w siblings are unsafe.
//!        (i.e., doing so may lead to multiple visits of the same node or
//!         some nodes remaining unvisited).
//!    Non-graph modifications are safe.

use crate::{
    basic_block::BasicBlock,
    context::{Context, Ptr},
    error::Result,
    linked_list::{ContainsLinkedList, LinkedList},
    operation::Operation,
    region::Region,
};

#[derive(Clone, Copy, Debug)]
/// Should the callback for a node be called before or after processing its children.
pub enum Order {
    /// Call the callback for a node before processing its children.
    PreOrder,
    /// Call the callback for a node after processing its children.
    PostOrder,
}

#[derive(Clone, Copy, Debug)]
/// The order in which children nodes are walked over.
pub enum Direction {
    /// Process nodes in lexicographic order.
    Forward,
    /// Process nodes in reverse lexicographic order.
    Reverse,
}

/// For an IR walk, specify the order of visiting different kinds of nodes.
pub struct WalkConfig {
    /// Order of processing [Region]s in an [Operation].
    pub regions_in_op: (Order, Direction),
    /// Order of processing [Operation]s in a [BasicBlock]
    pub ops_in_block: (Order, Direction),
    ///Order of processing [BasicBlock]s in a [Region]
    pub blocks_in_region: (Order, Direction),
}

/// The walker calls the callback for any of these IR entities.
pub enum IRNode {
    Operation(Ptr<Operation>),
    BasicBlock(Ptr<BasicBlock>),
    Region(Ptr<Region>),
}

/// The walker functions calls back to functions of this type.
pub type WalkerCallback<State> = fn(&mut Context, &mut State, IRNode) -> Result<()>;

/// Visit an [Operation] and walk its children [Region]s.
pub fn walk_op<State>(
    ctx: &mut Context,
    state: &mut State,
    config: &WalkConfig,
    root: Ptr<Operation>,
    callback: WalkerCallback<State>,
) -> Result<()> {
    if let Order::PreOrder = config.regions_in_op.0 {
        callback(ctx, state, IRNode::Operation(root))?
    }

    let range: Box<dyn Iterator<Item = usize>> = match config.regions_in_op.1 {
        Direction::Forward => Box::new(0..root.deref(ctx).num_regions()),
        Direction::Reverse => Box::new((0..root.deref(ctx).num_regions()).rev()),
    };

    for reg_idx in range {
        let region = root
            .deref(ctx)
            .get_region(reg_idx)
            .expect("Region deleted during walk");
        walk_region(ctx, state, config, region, callback)?
    }

    if let Order::PostOrder = config.regions_in_op.0 {
        callback(ctx, state, IRNode::Operation(root))?
    }

    Ok(())
}

/// Visit a [Region] and walk its children [BasicBlock]s.
pub fn walk_region<State>(
    ctx: &mut Context,
    state: &mut State,
    config: &WalkConfig,
    root: Ptr<Region>,
    callback: WalkerCallback<State>,
) -> Result<()> {
    if let Order::PreOrder = config.blocks_in_region.0 {
        callback(ctx, state, IRNode::Region(root))?
    }

    let mut cur_block_opt = match config.blocks_in_region.1 {
        Direction::Forward => root.deref(ctx).get_head(),
        Direction::Reverse => root.deref(ctx).get_tail(),
    };

    while let Some(cur_block) = cur_block_opt {
        walk_block(ctx, state, config, cur_block, callback)?;
        cur_block_opt = match config.blocks_in_region.1 {
            Direction::Forward => cur_block.deref(ctx).get_next(),
            Direction::Reverse => cur_block.deref(ctx).get_prev(),
        }
    }

    if let Order::PostOrder = config.blocks_in_region.0 {
        callback(ctx, state, IRNode::Region(root))?
    }

    Ok(())
}

/// Visit a [BasicBlock] and walk its children [Operation]s.
pub fn walk_block<State>(
    ctx: &mut Context,
    state: &mut State,
    config: &WalkConfig,
    root: Ptr<BasicBlock>,
    callback: WalkerCallback<State>,
) -> Result<()> {
    if let Order::PreOrder = config.ops_in_block.0 {
        callback(ctx, state, IRNode::BasicBlock(root))?
    }

    let mut cur_op_opt = match config.ops_in_block.1 {
        Direction::Forward => root.deref(ctx).get_head(),
        Direction::Reverse => root.deref(ctx).get_tail(),
    };

    while let Some(cur_op) = cur_op_opt {
        walk_op(ctx, state, config, cur_op, callback)?;
        cur_op_opt = match config.ops_in_block.1 {
            Direction::Forward => cur_op.deref(ctx).get_next(),
            Direction::Reverse => cur_op.deref(ctx).get_prev(),
        }
    }

    if let Order::PostOrder = config.ops_in_block.0 {
        callback(ctx, state, IRNode::BasicBlock(root))?
    }

    Ok(())
}

/// A preset config with [Order::PreOrder] and [Direction::Forward]
/// for all IR node kinds.
pub const WALKCONFIG_PREORDER_FORWARD: WalkConfig = WalkConfig {
    regions_in_op: (Order::PreOrder, Direction::Forward),
    ops_in_block: (Order::PreOrder, Direction::Forward),
    blocks_in_region: (Order::PreOrder, Direction::Forward),
};

/// A preset config with [Order::PostOrder] and [Direction::Forward]
/// for all IR node kinds.
pub const WALKCONFIG_POSTORDER_FORWARD: WalkConfig = WalkConfig {
    regions_in_op: (Order::PostOrder, Direction::Forward),
    ops_in_block: (Order::PostOrder, Direction::Forward),
    blocks_in_region: (Order::PostOrder, Direction::Forward),
};
