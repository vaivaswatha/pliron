use rustc_hash::FxHashSet;
use thiserror::Error;

use crate::context::Context;
use crate::context::Ptr;
use crate::debug_info::get_operation_result_name;
use crate::debug_info::set_operation_result_name;
use crate::operation::Operation;
use crate::use_def_lists::Value;

/// Listener to be invoked when PatternRewriter make changes
pub trait Listener {
    /// Notification handler for when an operation is inserted into the builder.
    /// `op` is the operation that was inserted.
    fn notify_operation_inserted(&mut self, op: Ptr<Operation>);

    /// This is called on an operation that a rewrite is erasing, right before
    /// the operation is deleted. At this point, the operation has zero uses.
    fn notify_operation_erased(&mut self, op: Ptr<Operation>);

    fn get_erased_ops(&self) -> &FxHashSet<Ptr<Operation>>;

    // TODO:: add more notifications (in-place modifications, replaced operations, etc.)
}

#[derive(Default)]
pub struct AccumulatingListener {
    pub inserted_ops: Vec<Ptr<Operation>>,
    pub erased_ops: FxHashSet<Ptr<Operation>>,
}

impl Listener for AccumulatingListener {
    fn notify_operation_inserted(&mut self, op: Ptr<Operation>) {
        self.inserted_ops.push(op);
    }

    fn notify_operation_erased(&mut self, op: Ptr<Operation>) {
        self.erased_ops.insert(op);
    }

    fn get_erased_ops(&self) -> &FxHashSet<Ptr<Operation>> {
        &self.erased_ops
    }
}

#[derive(Debug, Error)]
pub enum PatternRewriterError {
    #[error("Pattern match {pattern_name} failed with error: {error}")]
    PatternFailed {
        #[source]
        error: anyhow::Error,
        pattern_name: String,
    },
}

/// This class coordinates the application of a rewrite on a set of IR,
/// providing a way for clients to track mutations and create new operations.
/// This class serves as a common API for IR mutation between pattern rewrites
/// and non-pattern rewrites, and facilitates the development of shared
/// IR transformation utilities.
pub trait PatternRewriter {
    /// Sets the insertion point to the specified operation, which will cause
    /// subsequent insertions to go right before it.
    fn set_insertion_point(&mut self, op: Ptr<Operation>);

    /// Returns the current insertion point, or None if there is no insertion point.
    fn get_insertion_point(&self) -> Option<Ptr<Operation>>;

    /// Invokes the closure with the listener for this pattern rewriter.
    fn invoke_listener(&mut self, f: &dyn Fn(&mut dyn Listener));

    // /// Sets the listener for this pattern rewriter.
    // fn set_listener(&mut self, listener: L);

    /// Insert an operation at the current insertion point.
    fn insert(&mut self, ctx: &Context, op: Ptr<Operation>) -> Result<(), PatternRewriterError> {
        let insertion_point = self.get_insertion_point().unwrap();
        op.insert_before(ctx, insertion_point);
        self.invoke_listener(&|listener| {
            listener.notify_operation_inserted(op);
        });
        Ok(())
    }

    /// This method replaces the results of the operation with the specified list of
    /// values. The number of provided values must match the number of results of
    /// the operation.
    fn replace_op_with(
        &mut self,
        ctx: &mut Context,
        op: Ptr<Operation>,
        new_op: Ptr<Operation>,
    ) -> Result<(), PatternRewriterError> {
        let op_result_name = get_operation_result_name(ctx, op, 0);
        if let Some(op_result_name) = op_result_name {
            set_operation_result_name(ctx, new_op, 0, op_result_name);
        }
        let old_val_to_new_val_map: Vec<(Value, Value)> = op
            .deref(ctx)
            .results
            .iter()
            .map(Value::from)
            .zip(new_op.deref(ctx).results.iter().map(Value::from))
            .collect::<Vec<_>>();
        for (old_val, new_val) in old_val_to_new_val_map {
            old_val.replace_some_uses_with(ctx, |_, _| true, &new_val);
        }
        new_op.insert_after(ctx, op);
        self.erase_op(ctx, op)?;
        Ok(())
    }

    /// This method erases an operation that is known to have no uses. The uses of
    /// the given operation *must* be known to be dead.
    fn erase_op(
        &mut self,
        ctx: &mut Context,
        op: Ptr<Operation>,
    ) -> Result<(), PatternRewriterError> {
        self.invoke_listener(&|listener| {
            listener.notify_operation_erased(op);
        });
        Operation::erase(op, ctx);
        Ok(())
    }

    /// This method is a wrapper around a root update of an operation. It
    /// wraps calls to capture the op state diff around the given f.
    fn update_root_in_place(&self, f: &mut dyn FnMut()) -> Result<(), PatternRewriterError> {
        // TODO: hooks for capturing op state diff before and after
        f();
        Ok(())
    }
}

pub struct GenericPatternRewriter {
    insertion_point: Option<Ptr<Operation>>,
    listener: Option<Box<dyn Listener>>,
}

impl GenericPatternRewriter {
    pub fn new(listener: Option<Box<dyn Listener>>) -> Self {
        Self {
            insertion_point: None,
            listener,
        }
    }

    pub fn get_listener(&self) -> Option<&Box<dyn Listener>> {
        self.listener.as_ref()
    }
}

impl PatternRewriter for GenericPatternRewriter {
    fn set_insertion_point(&mut self, op: Ptr<Operation>) {
        self.insertion_point = Some(op);
    }

    fn get_insertion_point(&self) -> Option<Ptr<Operation>> {
        self.insertion_point
    }

    fn invoke_listener(&mut self, f: &dyn Fn(&mut dyn Listener)) {
        if let Some(listener) = &mut self.listener {
            f(listener.as_mut());
        }
    }
}

/// RewritePattern is a trait for all DAG to DAG replacements.
/// There are two possible usages of this trait:
///   * Multi-step RewritePattern with "match" and "rewrite"
///     - By overloading the "match" and "rewrite" functions, the user can
///       separate the concerns of matching and rewriting.
///   * Single-step RewritePattern with "matchAndRewrite"
///     - By overloading the "matchAndRewrite" function, the user can perform
///       the rewrite in the same call as the match.
pub trait RewritePattern {
    /// Attempt to match against code rooted at the specified operation,
    /// Returns true if the pattern was matched, false otherwise.
    fn match_op(&self, ctx: &Context, op: Ptr<Operation>) -> Result<bool, anyhow::Error>;

    /// Rewrite the IR rooted at the specified operation with the result of
    /// this pattern, generating any new operations with the specified
    /// builder. If an unexpected error is encountered (an internal
    /// compiler error), the IR is left in a valid state.
    fn rewrite(
        &self,
        ctx: &mut Context,
        op: Ptr<Operation>,
        rewriter: &mut dyn PatternRewriter,
    ) -> Result<(), anyhow::Error>;

    /// Attempt to match against code rooted at the specified operation.
    /// If successful, this function will automatically perform the rewrite.
    /// Returns true if the pattern was matched and rewrite was ran on the op, false otherwise.
    fn match_and_rewrite(
        &self,
        ctx: &mut Context,
        op: Ptr<Operation>,
        rewriter: &mut dyn PatternRewriter,
    ) -> Result<bool, anyhow::Error> {
        if self.match_op(ctx, op)? {
            self.rewrite(ctx, op, rewriter)?;
            Ok(true)
        } else {
            Ok(false)
        }
    }
}

#[cfg(test)]
mod tests {
    use apint::ApInt;

    use crate::dialects::builtin::attributes::IntegerAttr;
    use crate::dialects::builtin::ops::ConstantOp;
    use crate::dialects::builtin::types::IntegerType;
    use crate::dialects::builtin::types::Signedness;
    use crate::op::Op;

    use super::*;

    #[test]
    fn op_rewrite_pattern() {
        #[derive(Debug, Default)]
        pub struct ConstantOpLowering {}

        impl RewritePattern for ConstantOpLowering {
            fn match_op(&self, ctx: &Context, op: Ptr<Operation>) -> Result<bool, anyhow::Error> {
                Ok(op
                    .deref(ctx)
                    .get_op(ctx)
                    .downcast_ref::<ConstantOp>()
                    .is_some())
            }

            fn rewrite(
                &self,
                ctx: &mut Context,
                op: Ptr<Operation>,
                rewriter: &mut dyn PatternRewriter,
            ) -> Result<(), anyhow::Error> {
                let i64_ty = IntegerType::get(ctx, 64, Signedness::Signed);
                let zero_const = IntegerAttr::create(i64_ty, ApInt::from(0));
                let const_op = ConstantOp::new_unlinked(ctx, zero_const);
                rewriter.insert(ctx, const_op.get_operation())?;
                // const_op.get_operation().insert_before(ctx, op);
                rewriter.erase_op(ctx, op)?;
                Ok(())
            }
        }
    }
}
