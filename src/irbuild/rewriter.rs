//! [Rewriter] extends [Inserter] with more capabilities, such as replace and erase operations.

use crate::{
    basic_block::BasicBlock,
    context::{Context, Ptr},
    identifier::Identifier,
    irbuild::{
        inserter::{IRInserter, Inserter, OpInsertionPoint},
        listener::RewriteListener,
    },
    op::Op,
    operation::Operation,
    region::Region,
    r#type::TypeObj,
};

/// Rewriter interface for transformations.
/// Use `()` as the listener type if no listener is needed.
pub trait Rewriter<L: RewriteListener>: Inserter<L> {
    /// Replace an operation (and delete it) with another operation.
    /// Results of the new operation must match the results of the old operation.
    fn replace_operation(&mut self, ctx: &mut Context, op: Ptr<Operation>, new_op: Ptr<Operation>);

    /// Erase an operation. The operation must have no uses.
    fn erase_operation(&mut self, ctx: &mut Context, op: Ptr<Operation>);

    /// Has the IR been modified via this rewriter?
    fn is_modified(&self) -> bool;

    /// Set that the IR has been modified via this rewriter.
    fn set_modified(&mut self);

    /// Clear the modified flag.
    fn clear_modified(&mut self);
}

/// An implementation of the rewriter trait.
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

    fn create_block_before(
        &mut self,
        ctx: &mut Context,
        mark: Ptr<BasicBlock>,
        label: Option<Identifier>,
        arg_types: Vec<Ptr<TypeObj>>,
    ) {
        self.inserter
            .create_block_before(ctx, mark, label, arg_types)
    }

    fn create_block_after(
        &mut self,
        ctx: &mut Context,
        mark: Ptr<BasicBlock>,
        label: Option<Identifier>,
        arg_types: Vec<Ptr<TypeObj>>,
    ) {
        self.inserter
            .create_block_after(ctx, mark, label, arg_types)
    }

    fn create_block_at_start(
        &mut self,
        ctx: &mut Context,
        region: Ptr<Region>,
        label: Option<Identifier>,
        arg_types: Vec<Ptr<TypeObj>>,
    ) {
        self.inserter
            .create_block_at_start(ctx, region, label, arg_types)
    }

    fn create_block_at_end(
        &mut self,
        ctx: &mut Context,
        region: Ptr<Region>,
        label: Option<Identifier>,
        arg_types: Vec<Ptr<TypeObj>>,
    ) {
        self.inserter
            .create_block_at_end(ctx, region, label, arg_types)
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
        if let Some(listener) = self.inserter.get_listener_mut() {
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
        if let Some(listener) = self.inserter.get_listener_mut() {
            listener.notify_operation_erasure(ctx, op);
        }
        Operation::erase(op, ctx);
        self.set_modified();
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
