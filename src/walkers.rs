//! Various walker configurations, for use with [crate::walker]

use rustc_hash::FxHashSet;

use crate::{
    basic_block::BasicBlock,
    context::{Context, Ptr},
    error::Result,
    linked_list::ContainsLinkedList,
    operation::Operation,
    region::Region,
    walker::{
        ProcessBlock, ProcessOperation, ProcessRegion, VisitAction, VisitBlock, VisitOperation,
        VisitRegion,
    },
};

/// Visit the control-flow-graph (of a [Region]) in pre-order.
/// A state of already visited [BasicBlock]s is maintained to ensure termination.
#[derive(Default)]
pub struct PreOrderCFG {
    /// The set of blocks that we've already visited.
    visited: FxHashSet<Ptr<BasicBlock>>,
}

impl PreOrderCFG {
    /// Clear the set of blocks marked as already visited.
    pub fn reset(&mut self) {
        self.visited.clear();
    }
}

impl VisitBlock for PreOrderCFG {
    fn blocks_visit_order(
        &mut self,
        ctx: &Context,
        cur_block: Ptr<BasicBlock>,
    ) -> Vec<VisitAction<Ptr<BasicBlock>>> {
        if self.visited.contains(&cur_block) {
            return vec![];
        }
        let mut blocks = vec![VisitAction::Process];
        blocks.extend(
            cur_block
                .deref(ctx)
                .successors(ctx)
                .into_iter()
                .map(VisitAction::Visit),
        );
        blocks
    }

    fn operations_visit_order(
        &mut self,
        ctx: &Context,
        cur_block: Ptr<BasicBlock>,
    ) -> Vec<Ptr<Operation>> {
        cur_block.deref(ctx).iter(ctx).collect()
    }
}

/// At every node, process the node first,
/// and then its successor or children.
pub struct PreOrderVisitor {
    cfg: PreOrderCFG,
}

impl Default for PreOrderVisitor {
    fn default() -> Self {
        Self::new()
    }
}

impl PreOrderVisitor {
    pub fn new() -> Self {
        PreOrderVisitor {
            cfg: PreOrderCFG::default(),
        }
    }
}

// Delegate to self.cfg
impl VisitBlock for PreOrderVisitor {
    fn blocks_visit_order(
        &mut self,
        ctx: &Context,
        cur_block: Ptr<BasicBlock>,
    ) -> Vec<VisitAction<Ptr<BasicBlock>>> {
        self.cfg.blocks_visit_order(ctx, cur_block)
    }

    fn operations_visit_order(
        &mut self,
        ctx: &Context,
        cur_block: Ptr<BasicBlock>,
    ) -> Vec<Ptr<Operation>> {
        self.cfg.operations_visit_order(ctx, cur_block)
    }
}

impl VisitOperation for PreOrderVisitor {
    fn region_visit_order(
        &mut self,
        ctx: &Context,
        cur_operation: Ptr<Operation>,
    ) -> Vec<Ptr<Region>> {
        cur_operation.deref(ctx).regions().collect()
    }
}

impl VisitRegion for PreOrderVisitor {
    fn blocks_visit_order(
        &mut self,
        ctx: &Context,
        cur_region: Ptr<Region>,
    ) -> Vec<Ptr<BasicBlock>> {
        self.cfg.reset();
        cur_region
            .deref(ctx)
            .get_head()
            .map(|entry| vec![entry])
            .unwrap_or_default()
    }
}

/// A callback to process an [Operation], with the walker at `State`.
pub type OpCallback<State> = fn(&mut State, &mut Context, Ptr<Operation>) -> Result<()>;
/// A callback to process a [BasicBlock], with the walker at `State`.
pub type BlockCallback<State> = fn(&mut State, &mut Context, Ptr<BasicBlock>) -> Result<()>;
/// A callback to process an [Region], with the walker at `State`.
pub type RegionCallback<State> = fn(&mut State, &mut Context, Ptr<Region>) -> Result<()>;

pub struct PreOrderProcessor<State> {
    pub state: State,
    op_callback: OpCallback<State>,
    block_callback: BlockCallback<State>,
    region_callback: RegionCallback<State>,
}

impl<State> PreOrderProcessor<State> {
    pub fn new(
        state: State,
        op_callback: OpCallback<State>,
        block_callback: BlockCallback<State>,
        region_callback: RegionCallback<State>,
    ) -> Self {
        PreOrderProcessor {
            state,
            op_callback,
            block_callback,
            region_callback,
        }
    }
}

impl<State> ProcessOperation for PreOrderProcessor<State> {
    fn process_pre_regions(&mut self, ctx: &mut Context, operation: Ptr<Operation>) -> Result<()> {
        (self.op_callback)(&mut self.state, ctx, operation)
    }
}

impl<State> ProcessBlock for PreOrderProcessor<State> {
    fn process_pre_insts(&mut self, ctx: &mut Context, block: Ptr<BasicBlock>) -> Result<()> {
        (self.block_callback)(&mut self.state, ctx, block)
    }
}

impl<State> ProcessRegion for PreOrderProcessor<State> {
    fn process_pre_blocks(&mut self, ctx: &mut Context, region: Ptr<Region>) -> Result<()> {
        (self.region_callback)(&mut self.state, ctx, region)
    }
}
