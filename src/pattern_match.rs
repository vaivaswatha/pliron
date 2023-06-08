use crate::context::Context;
use crate::context::Ptr;
use crate::debug_info::get_operation_result_name;
use crate::debug_info::set_operation_result_name;
use crate::error::CompilerError;
use crate::operation::Operation;
use crate::use_def_lists::Value;

/// Listener to be invoked when PatternRewriter make changes
pub trait Listener {
    /// Notification handler for when an operation is inserted into the builder.
    /// `op` is the operation that was inserted.
    fn notify_operation_inserted(&mut self, op: Ptr<Operation>);

    /// This is called on an operation that a rewrite is removing, right before
    /// the operation is deleted. At this point, the operation has zero uses.
    fn notify_operation_removed(&mut self, op: Ptr<Operation>);

    // TODO:: add more notifications (in-place modifications, replaced operations, etc.)
}

#[derive(Default)]
pub struct AccumulatingListener {
    pub inserted_ops: Vec<Ptr<Operation>>,
    pub removed_ops: Vec<Ptr<Operation>>,
}

impl Listener for AccumulatingListener {
    fn notify_operation_inserted(&mut self, op: Ptr<Operation>) {
        self.inserted_ops.push(op);
    }

    fn notify_operation_removed(&mut self, op: Ptr<Operation>) {
        self.removed_ops.push(op);
    }
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
    fn insert(&mut self, ctx: &Context, op: Ptr<Operation>) -> Result<(), CompilerError> {
        if let Some(insertion_point) = &self.get_insertion_point() {
            op.insert_before(ctx, *insertion_point);
            self.invoke_listener(&|listener| {
                listener.notify_operation_inserted(op);
            });
        } else {
            return Err(CompilerError::VerificationError {
                msg: "OpBuilder::create failed. No insertion point set for pattern rewriter"
                    .to_string(),
            });
        };
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
    ) -> Result<(), CompilerError> {
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
    fn erase_op(&mut self, ctx: &mut Context, op: Ptr<Operation>) -> Result<(), CompilerError> {
        self.invoke_listener(&|listener| {
            listener.notify_operation_removed(op);
        });
        Operation::erase(op, ctx);
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

/// The result of the pattern match.
pub enum MatchResult {
    /// The pattern match failed.
    Fail,
    /// The pattern match succeeded.
    Success,
}

impl MatchResult {
    pub fn is_success(&self) -> bool {
        match self {
            MatchResult::Success => true,
            MatchResult::Fail => false,
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
    fn match_op(&self, ctx: &Context, op: Ptr<Operation>) -> MatchResult;

    /// Rewrite the IR rooted at the specified operation with the result of
    /// this pattern, generating any new operations with the specified
    /// builder. If an unexpected error is encountered (an internal
    /// compiler error), the IR is left in a valid state.
    fn rewrite(
        &self,
        ctx: &mut Context,
        op: Ptr<Operation>,
        rewriter: &mut dyn PatternRewriter,
    ) -> Result<(), CompilerError>;

    /// Attempt to match against code rooted at the specified operation.
    /// If successful, this function will automatically perform the rewrite.
    fn match_and_rewrite(
        &self,
        ctx: &mut Context,
        op: Ptr<Operation>,
        rewriter: &mut dyn PatternRewriter,
    ) -> Result<MatchResult, CompilerError> {
        let res = self.match_op(ctx, op);
        match res {
            MatchResult::Fail => (),
            MatchResult::Success => {
                self.rewrite(ctx, op, rewriter)?;
            }
        };
        Ok(res)
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
            fn match_op(&self, ctx: &Context, op: Ptr<Operation>) -> MatchResult {
                if op
                    .deref(ctx)
                    .get_op(ctx)
                    .downcast_ref::<ConstantOp>()
                    .is_some()
                {
                    MatchResult::Success
                } else {
                    MatchResult::Fail
                }
            }

            fn rewrite(
                &self,
                ctx: &mut Context,
                op: Ptr<Operation>,
                rewriter: &mut dyn PatternRewriter,
            ) -> Result<(), CompilerError> {
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
