//! An IR insertion utility

use crate::{
    basic_block::BasicBlock,
    context::{Context, Ptr},
    op::Op,
    operation::Operation,
};

enum InsertionPoint {
    AtBlockStart(Ptr<BasicBlock>),
    AfterOperation(Ptr<Operation>),
}

pub struct IRInserter {
    insertion_point: InsertionPoint,
}

impl IRInserter {
    /// Creates a new [IRInserter] that inserts the next operation
    /// at the start of the given [BasicBlock].
    pub fn new_at_block_start(block: Ptr<BasicBlock>) -> Self {
        Self {
            insertion_point: InsertionPoint::AtBlockStart(block),
        }
    }

    /// Creates a new [IRInserter] that inserts the next operation
    /// after the given [Operation].
    pub fn new_after_operation(op: Ptr<Operation>) -> Self {
        Self {
            insertion_point: InsertionPoint::AfterOperation(op),
        }
    }

    /// Appends an [Operation] at the current insertion point,
    /// updating the insertion point accordingly.
    pub fn append_operation(&mut self, ctx: &Context, operation: Ptr<Operation>) {
        match self.insertion_point {
            InsertionPoint::AtBlockStart(block) => {
                // Insert operation at the start of the block
                operation.insert_at_front(block, ctx);
            }
            InsertionPoint::AfterOperation(op) => {
                // Insert operation after the specified operation
                operation.insert_after(ctx, op);
            }
        }
        // Update the insertion point to be after the newly inserted operation
        self.insertion_point = InsertionPoint::AfterOperation(operation);
    }

    /// Appends an [Op] at the current insertion point,
    /// updating the insertion point accordingly.
    pub fn append_op(&mut self, ctx: &Context, op: impl Op) {
        let operation = op.get_operation();
        self.append_operation(ctx, operation);
    }
}
