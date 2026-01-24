use crate::{
    basic_block::BasicBlock,
    context::{Context, Ptr},
    graph::walkers::{IRNode, WALKCONFIG_PREORDER_FORWARD, immutable::walk_op},
    identifier::Identifier,
    inserter::{IRInserter, Inserter, OpInsertionPoint},
    op::Op,
    operation::Operation,
    region::Region,
    result::Result,
    r#type::TypeObj,
};

/// Rewriter interface for transformations.
pub trait Rewriter: Inserter {
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
#[derive(Default)]
pub struct IRRewriter<I: Inserter = IRInserter> {
    inserter: I,
    modified: bool,
}

impl<I: Inserter> Inserter for IRRewriter<I> {
    fn append_operation(&mut self, ctx: &Context, operation: Ptr<Operation>) {
        self.inserter.append_operation(ctx, operation)
    }

    fn append_op(&mut self, ctx: &Context, op: impl Op) {
        self.inserter.append_op(ctx, op)
    }

    fn insert_operation(&self, ctx: &Context, operation: Ptr<Operation>) {
        self.inserter.insert_operation(ctx, operation)
    }

    fn insert_op(&self, ctx: &Context, op: impl Op) {
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
}

impl<I: Inserter> Rewriter for IRRewriter<I> {
    fn replace_operation(&mut self, ctx: &mut Context, op: Ptr<Operation>, new_op: Ptr<Operation>) {
        assert!(
            op.deref(ctx).get_num_results() == new_op.deref(ctx).get_num_results(),
            "Replacement operation must have the same number of results as the original operation."
        );
        // We need to collect the results first to avoid `RefCell` borrowing issues.
        let results: Vec<_> = op
            .deref(ctx)
            .results()
            .zip(new_op.deref(ctx).results())
            .collect();
        for (res, new_res) in results {
            res.replace_all_uses_with(ctx, &new_res);
        }
        Operation::erase(op, ctx);
        self.set_modified();
    }

    fn erase_operation(&mut self, ctx: &mut Context, op: Ptr<Operation>) {
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

/// Match operations and rewrite them.
pub trait MatchRewrite<R: Rewriter = IRRewriter> {
    /// Should operation be rewritten?
    fn r#match(&mut self, ctx: &Context, op: Ptr<Operation>) -> bool;
    /// Rewrite the matched operation.
    /// Insertion point is set to be before the operation being rewritten.
    fn rewrite(&mut self, ctx: &mut Context, rewriter: &mut R, op: Ptr<Operation>) -> Result<()>;
}

/// Collects all operations (recursively) that match a given pattern
/// and then applies a rewrite to them.
pub fn collect_rewrite<R: Rewriter, M: MatchRewrite<R>>(
    ctx: &mut Context,
    mut match_rewrite: M,
    mut rewriter: R,
    op: Ptr<Operation>,
) -> Result<()> {
    // Collect all operations that match.
    let mut to_rewrite = Vec::new();
    struct WalkerState<'a, M> {
        match_rewrite: &'a mut M,
        to_rewrite: &'a mut Vec<Ptr<Operation>>,
    }
    let mut state = WalkerState {
        match_rewrite: &mut match_rewrite,
        to_rewrite: &mut to_rewrite,
    };

    // A callback for the walker.
    fn walker_callback<R: Rewriter, M: MatchRewrite<R>>(
        ctx: &Context,
        state: &mut WalkerState<M>,
        node: IRNode,
    ) {
        if let IRNode::Operation(op) = node
            && state.match_rewrite.r#match(ctx, op)
        {
            state.to_rewrite.push(op);
        }
    }

    // Walk the operation tree.
    walk_op(
        ctx,
        &mut state,
        &WALKCONFIG_PREORDER_FORWARD,
        op,
        walker_callback,
    );

    // Now rewrite all collected operations.
    for op in to_rewrite {
        // TODO: Use a Listener to see if the operation was deleted during rewriting.
        rewriter.set_insertion_point(OpInsertionPoint::BeforeOperation(op));
        match_rewrite.rewrite(ctx, &mut rewriter, op)?;
    }
    Ok(())
}
