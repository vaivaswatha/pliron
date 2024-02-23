//! A walker traverses the graph, visiting each node (region, block and op).
//! At each node, it calls the provided callbacks to process the node.
//!
//! Visit: When a walk arrives at a node, it is called visiting the node.
//!   Visiting a node includes processing it and visiting other related
//!   entities, based on the node type.
//!
//! Process: As part of visiting a node, the node itself must be processed.
//!   This is essentially calling back a provided function with the node as
//!   argument.
//!
//! Modifications: At each node, the list of children or successor/predecessor
//!   nodes, to be visited, is collected first, before any of them are visited.
//!   So any modifications, insertions or deletions to the graph must take this
//!   into account, to avoid visiting deleted nodes or missing visits to newly
//!   inserted nodes.
//!
//! Termination: Cycles are possible b/w the blocks in a region.
//!   It is the responsiblity of the [VisitBlock::blocks_visit_order] to ensure
//!   termination. No cycle detection is done by the walker.

use crate::{
    basic_block::BasicBlock,
    context::{Context, Ptr},
    error::Result,
    operation::Operation,
    region::Region,
};

/// When the walker arrives at a node, it calls the Visit*
/// callbacks, that return a list of [VisitAction], and does that.
pub enum VisitAction<T> {
    /// Process the node being visited.
    Process,
    /// Visit other nodes.
    Visit(T),
}

/// When a walk arrives at a [BasicBlock], this trait decides when its
/// successors / predecessors are visited, and when the block itself be processed.
pub trait VisitBlock {
    /// Given a block, determine when the successor/predecessor blocks are visited
    /// and when the block itself is processed.
    fn blocks_visit_order(
        &mut self,
        ctx: &Context,
        cur_block: Ptr<BasicBlock>,
    ) -> Vec<VisitAction<Ptr<BasicBlock>>>;

    /// Given a block, get the list of [Operation]s in the block that must be visited.
    fn operations_visit_order(
        &mut self,
        ctx: &Context,
        cur_block: Ptr<BasicBlock>,
    ) -> Vec<Ptr<Operation>>;
}

/// Callbacks when a [BasicBlock] is processed.
pub trait ProcessBlock {
    /// Call back before visiting the instructions in a [BasicBlock].
    fn process_pre_insts(&mut self, _ctx: &mut Context, _block: Ptr<BasicBlock>) -> Result<()> {
        Ok(())
    }
    /// Call back after visiting the instructions in a [BasicBlock].
    fn process_post_insts(&mut self, _ctx: &mut Context, _block: Ptr<BasicBlock>) -> Result<()> {
        Ok(())
    }
}

/// When a walk arrives at a [Region], specify which of its blocks, and in what
/// order, must be visited.
pub trait VisitRegion {
    /// Given a region, get a list of child blocks that must be visited.
    /// Typically, this is just the entry block or the exit blocks since
    /// the other blocks subsequently get visited via [VisitBlock::blocks_visit_order].
    fn blocks_visit_order(
        &mut self,
        ctx: &Context,
        cur_region: Ptr<Region>,
    ) -> Vec<Ptr<BasicBlock>>;
}

/// Callbacks when a [Region] is processed.
pub trait ProcessRegion {
    /// Call back before visiting the [BasicBlock]s in a [Region].
    fn process_pre_blocks(&mut self, _ctx: &mut Context, _region: Ptr<Region>) -> Result<()> {
        Ok(())
    }
    /// Call back after visiting the [BasicBlock]s in a [Region].
    fn process_post_blocks(&mut self, _ctx: &mut Context, _region: Ptr<Region>) -> Result<()> {
        Ok(())
    }
}

/// When a walk arrives at an [Operation],
/// specify the order in which its [Region]s are visited.
pub trait VisitOperation {
    /// Given an [Operation], get a list of child [Region]s to be visited, in that order.
    fn region_visit_order(
        &mut self,
        ctx: &Context,
        cur_operation: Ptr<Operation>,
    ) -> Vec<Ptr<Region>>;
}

/// Callbacks when an [Operation] is processed.
pub trait ProcessOperation {
    /// Call back before visiting the [Region]s in an [Operation].
    fn process_pre_regions(
        &mut self,
        _ctx: &mut Context,
        _operation: Ptr<Operation>,
    ) -> Result<()> {
        Ok(())
    }
    /// Call back after visiting the [Region]s in an [Operation].
    fn process_post_regions(
        &mut self,
        _ctx: &mut Context,
        _operation: Ptr<Operation>,
    ) -> Result<()> {
        Ok(())
    }
}

/// Given Visitors and Processors (see [module documentation](crate::walker)),
/// walk the entire IR graph, starting at a provided root node.
pub struct Walker<Visitor, Processor>
where
    Visitor: VisitBlock + VisitOperation + VisitRegion,
    Processor: ProcessBlock + ProcessOperation + ProcessRegion,
{
    pub visitor: Visitor,
    pub processor: Processor,
}

impl<Visitor, Processor> Walker<Visitor, Processor>
where
    Visitor: VisitBlock + VisitOperation + VisitRegion,
    Processor: ProcessBlock + ProcessOperation + ProcessRegion,
{
    /// Visit an operation, calling back the processors before and after visits of nested regions.
    pub fn walk_operation(&mut self, ctx: &mut Context, operation: Ptr<Operation>) -> Result<()> {
        self.processor.process_pre_regions(ctx, operation)?;
        for region in self.visitor.region_visit_order(ctx, operation) {
            self.walk_region(ctx, region)?;
        }
        self.processor.process_post_regions(ctx, operation)
    }

    /// Visit a region, calling back the processors before and after visiting nested blocks.
    pub fn walk_region(&mut self, ctx: &mut Context, region: Ptr<Region>) -> Result<()> {
        self.processor.process_pre_blocks(ctx, region)?;
        for block in VisitRegion::blocks_visit_order(&mut self.visitor, ctx, region) {
            self.walk_block(ctx, block)?
        }
        self.processor.process_post_blocks(ctx, region)
    }

    /// Visit successors / predecessors of a block and call back the block's processors
    /// before and after visiting the nested operations. The relative order of self processing and
    /// successor / predecessor block visits are determined by [VisitBlock::blocks_visit_order].
    pub fn walk_block(&mut self, ctx: &mut Context, block: Ptr<BasicBlock>) -> Result<()> {
        for action in VisitBlock::blocks_visit_order(&mut self.visitor, ctx, block) {
            match action {
                VisitAction::Process => {
                    self.processor.process_pre_insts(ctx, block)?;
                    for op in self.visitor.operations_visit_order(ctx, block) {
                        self.walk_operation(ctx, op)?;
                    }
                }
                VisitAction::Visit(next_block) => {
                    self.walk_block(ctx, next_block)?;
                }
            }
        }
        Ok(())
    }

    pub fn new(visitor: Visitor, processor: Processor) -> Self {
        Walker { processor, visitor }
    }
}
