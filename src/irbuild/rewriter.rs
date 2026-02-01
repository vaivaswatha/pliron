//! [Rewriter] extends [Inserter] with more capabilities, such as replace and erase operations.

use std::vec;

use crate::{
    basic_block::BasicBlock,
    common_traits::Named,
    context::{Context, Ptr},
    graph::traversals::region::post_order,
    identifier::{Identifier, underscore},
    irbuild::{
        inserter::{BlockInsertionPoint, IRInserter, Inserter, OpInsertionPoint},
        listener::RewriteListener,
    },
    linked_list::{ContainsLinkedList, LinkedList},
    op::Op,
    operation::Operation,
    region::Region,
    r#type::TypeObj,
};

/// Rewriter interface for transformations.
/// Use [DummyListener](super::listener::DummyListener) if no listener is needed.
pub trait Rewriter<L: RewriteListener>: Inserter<L> {
    /// Replace an [Operation] (and delete it) with another operation.
    /// Results of the new operation must match the results of the old operation.
    fn replace_operation(&mut self, ctx: &mut Context, op: Ptr<Operation>, new_op: Ptr<Operation>);

    /// Erase an [Operation]. The operation must have no uses.
    fn erase_operation(&mut self, ctx: &mut Context, op: Ptr<Operation>);

    /// Erase a [BasicBlock]. The block must have no uses.
    fn erase_block(&mut self, ctx: &mut Context, block: Ptr<BasicBlock>);

    /// Erase a [Region]. Affects the index of all regions after it.
    fn erase_region(&mut self, ctx: &mut Context, region: Ptr<Region>);

    /// Unlink an [Operation] from its current position
    fn unlink_operation(&mut self, ctx: &Context, op: Ptr<Operation>);

    /// Unlink a [BasicBlock] from its current position
    fn unlink_block(&mut self, ctx: &Context, block: Ptr<BasicBlock>);

    /// Move an [Operation] to a new insertion point.
    fn move_operation(&mut self, ctx: &Context, op: Ptr<Operation>, new_point: OpInsertionPoint);

    /// Move a [BasicBlock] to a new insertion point.
    fn move_block(&mut self, ctx: &Context, block: Ptr<BasicBlock>, new_point: BlockInsertionPoint);

    /// Split a [BasicBlock] at the given position.
    fn split_block(
        &mut self,
        ctx: &mut Context,
        block: Ptr<BasicBlock>,
        position: OpInsertionPoint,
    ) -> Ptr<BasicBlock>;

    /// Has the IR been modified via this rewriter?
    fn is_modified(&self) -> bool;

    /// Set that the IR has been modified via this rewriter.
    fn set_modified(&mut self);

    /// Clear the modified flag.
    fn clear_modified(&mut self);
}

/// An implementation of the rewriter trait.
/// Use [DummyListener](super::listener::DummyListener) if no listener is needed.
pub struct IRRewriter<L: RewriteListener, I: Inserter<L> = IRInserter<L>> {
    inserter: I,
    modified: bool,
    _phantom: std::marker::PhantomData<L>,
}

impl<L: RewriteListener, I: Inserter<L>> Default for IRRewriter<L, I>
where
    I: Default,
{
    fn default() -> Self {
        Self {
            inserter: I::default(),
            modified: false,
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<L: RewriteListener, I: Inserter<L>> Inserter<L> for IRRewriter<L, I> {
    fn append_operation(&mut self, ctx: &Context, operation: Ptr<Operation>) {
        self.inserter.append_operation(ctx, operation)
    }

    fn append_op(&mut self, ctx: &Context, op: impl Op) {
        self.inserter.append_op(ctx, op)
    }

    fn insert_operation(&mut self, ctx: &Context, operation: Ptr<Operation>) {
        self.inserter.insert_operation(ctx, operation)
    }

    fn insert_op(&mut self, ctx: &Context, op: impl Op) {
        self.inserter.insert_op(ctx, op)
    }

    fn insert_block(
        &mut self,
        ctx: &Context,
        insertion_point: BlockInsertionPoint,
        block: Ptr<BasicBlock>,
    ) {
        self.inserter.insert_block(ctx, insertion_point, block)
    }

    fn create_block(
        &mut self,
        ctx: &mut Context,
        insertion_point: BlockInsertionPoint,
        label: Option<Identifier>,
        arg_types: Vec<Ptr<TypeObj>>,
    ) -> Ptr<BasicBlock> {
        self.inserter
            .create_block(ctx, insertion_point, label, arg_types)
    }

    fn get_insertion_point(&self) -> OpInsertionPoint {
        self.inserter.get_insertion_point()
    }

    fn get_insertion_block(&self, ctx: &Context) -> Ptr<BasicBlock> {
        self.inserter.get_insertion_block(ctx)
    }

    fn set_insertion_point(&mut self, point: OpInsertionPoint) {
        self.inserter.set_insertion_point(point)
    }

    fn set_listener(&mut self, listener: L) {
        self.inserter.set_listener(listener);
    }

    fn get_listener(&self) -> Option<&L> {
        self.inserter.get_listener()
    }

    fn get_listener_mut(&mut self) -> Option<&mut L> {
        self.inserter.get_listener_mut()
    }
}

impl<L: RewriteListener, I: Inserter<L>> Rewriter<L> for IRRewriter<L, I> {
    fn replace_operation(&mut self, ctx: &mut Context, op: Ptr<Operation>, new_op: Ptr<Operation>) {
        assert!(
            op.deref(ctx).get_num_results() == new_op.deref(ctx).get_num_results(),
            "Replacement operation must have the same number of results as the original operation."
        );
        if let Some(listener) = self.get_listener_mut() {
            listener.notify_operation_replacement(ctx, op, new_op);
        }
        // We need to collect the results first to avoid `RefCell` borrowing issues.
        let results: Vec<_> = op
            .deref(ctx)
            .results()
            .zip(new_op.deref(ctx).results())
            .collect();
        for (res, new_res) in results {
            res.replace_all_uses_with(ctx, &new_res);
        }
        self.erase_operation(ctx, op);
        self.set_modified();
    }

    fn erase_operation(&mut self, ctx: &mut Context, op: Ptr<Operation>) {
        // We need to intervene and erase sub-entities only when there's a listener.
        // Otherwise `Operation::erase` later on will take care of it.
        if self.get_listener().is_some() {
            let regions = op.deref(ctx).regions().collect::<Vec<_>>();
            for region in regions.into_iter().rev() {
                self.erase_region(ctx, region);
            }
        }

        if let Some(listener) = self.get_listener_mut() {
            listener.notify_operation_erasure(ctx, op);
        }

        Operation::erase(op, ctx);
        self.set_modified();
    }

    fn erase_block(&mut self, ctx: &mut Context, block: Ptr<BasicBlock>) {
        // We need to intervene and erase sub-entities only when there's a listener.
        // Otherwise `BasicBlock::erase` later on will take care of it.
        if self.get_listener().is_some() {
            let operations = block.deref(ctx).iter(ctx).collect::<Vec<_>>();
            // We erase operations in reverse order so that uses are erased before defs.
            for op in operations.into_iter().rev() {
                self.erase_operation(ctx, op);
            }
        }

        if let Some(listener) = self.get_listener_mut() {
            listener.notify_block_erasure(ctx, block);
        }

        BasicBlock::erase(block, ctx);
        self.set_modified();
    }

    fn erase_region(&mut self, ctx: &mut Context, region: Ptr<Region>) {
        // We need to intervene and erase sub-entities only when there's a listener.
        // Otherwise `Region::erase` later on will take care of it.
        if self.get_listener().is_some() {
            // We erase blocks in post-order so that uses are erased before defs.
            let blocks = post_order(ctx, region);
            for block in blocks.iter().rev() {
                // We do not erase the block already because its predecessors
                // (which are its uses) haven't already been erased. We erase
                // only the operations now and the blocks later.
                let operations = block.deref(ctx).iter(ctx).collect::<Vec<_>>();
                // We erase operations in reverse order so that uses are erased before defs.
                for op in operations.into_iter().rev() {
                    self.erase_operation(ctx, op);
                }
            }
            // Now erase the blocks.
            for block in blocks {
                self.erase_block(ctx, block);
            }
        }

        if let Some(listener) = self.get_listener_mut() {
            listener.notify_region_erasure(ctx, region);
        }

        let index_in_parent = region.deref(ctx).get_index_in_parent(ctx);
        let parent_op = region.deref(ctx).get_parent_op();
        Operation::erase_region(parent_op, ctx, index_in_parent);
        self.set_modified();
    }

    fn unlink_operation(&mut self, ctx: &Context, op: Ptr<Operation>) {
        if let Some(listener) = self.get_listener_mut() {
            listener.notify_operation_unlinking(ctx, op);
        }
        op.unlink(ctx);
        self.set_modified();
    }

    fn unlink_block(&mut self, ctx: &Context, block: Ptr<BasicBlock>) {
        if let Some(listener) = self.get_listener_mut() {
            listener.notify_block_unlinking(ctx, block);
        }
        block.unlink(ctx);
        self.set_modified();
    }

    fn move_operation(&mut self, ctx: &Context, op: Ptr<Operation>, new_point: OpInsertionPoint) {
        self.unlink_operation(ctx, op);
        ScopedRewriter::new(self, new_point).insert_operation(ctx, op);
    }

    fn move_block(
        &mut self,
        ctx: &Context,
        block: Ptr<BasicBlock>,
        new_point: BlockInsertionPoint,
    ) {
        self.unlink_block(ctx, block);
        self.insert_block(ctx, new_point, block);
    }

    fn split_block(
        &mut self,
        ctx: &mut Context,
        block: Ptr<BasicBlock>,
        position: OpInsertionPoint,
    ) -> Ptr<BasicBlock> {
        // `create_block` below sets the insert point to the new block, so we save and restore it.
        let mut rewriter = ScopedRewriter::new(self, OpInsertionPoint::Unset);
        let label = block
            .deref(ctx)
            .given_name(ctx)
            .map(|label| label + underscore() + "split".try_into().unwrap());

        let new_block =
            rewriter.create_block(ctx, BlockInsertionPoint::AfterBlock(block), label, vec![]);
        let first_op_opt = match position {
            OpInsertionPoint::AtBlockStart(target_block) => {
                target_block.deref(ctx).iter(ctx).next()
            }
            OpInsertionPoint::AtBlockEnd(_target_block) => None,
            OpInsertionPoint::BeforeOperation(op) => Some(op),
            OpInsertionPoint::AfterOperation(op) => op.deref(ctx).get_next(),
            OpInsertionPoint::Unset => panic!("Cannot split block at unset insertion point."),
        };
        let mut current_op_opt = first_op_opt;
        while let Some(current_op) = current_op_opt {
            let next_op = current_op.deref(ctx).get_next();
            rewriter.move_operation(ctx, current_op, OpInsertionPoint::AtBlockEnd(new_block));
            current_op_opt = next_op;
        }
        new_block
    }

    fn is_modified(&self) -> bool {
        self.modified
    }

    fn set_modified(&mut self) {
        self.modified = true;
    }

    fn clear_modified(&mut self) {
        self.modified = false;
    }
}

/// A scoped rewriter that sets the insertion point for the duration of its lifetime.
/// On drop, it restores the previous insertion point.
/// The rewriter can be used as a normal rewriter via [Deref](std::ops::Deref).
pub struct ScopedRewriter<'a, L: RewriteListener, I: Inserter<L>> {
    rewriter: &'a mut IRRewriter<L, I>,
    prev_insertion_point: OpInsertionPoint,
}

impl<'a, L: RewriteListener, I: Inserter<L>> ScopedRewriter<'a, L, I> {
    pub fn new(rewriter: &'a mut IRRewriter<L, I>, insertion_point: OpInsertionPoint) -> Self {
        let prev_insertion_point = rewriter.get_insertion_point();
        rewriter.set_insertion_point(insertion_point);
        Self {
            rewriter,
            prev_insertion_point,
        }
    }
}

impl<'a, L: RewriteListener, I: Inserter<L>> Drop for ScopedRewriter<'a, L, I> {
    fn drop(&mut self) {
        self.rewriter.set_insertion_point(self.prev_insertion_point);
    }
}

impl<'a, L: RewriteListener, I: Inserter<L>> std::ops::Deref for ScopedRewriter<'a, L, I> {
    type Target = IRRewriter<L, I>;

    fn deref(&self) -> &Self::Target {
        self.rewriter
    }
}
impl<'a, L: RewriteListener, I: Inserter<L>> std::ops::DerefMut for ScopedRewriter<'a, L, I> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.rewriter
    }
}
