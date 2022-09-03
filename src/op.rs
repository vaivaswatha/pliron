use downcast_rs::{impl_downcast, Downcast};

use crate::{
    common_traits::{Stringable, Verify},
    context::Ptr,
    operation::Operation,
};

/// A wrapper around Operation for Op(code) specific work.
/// All per-instance data must be in underyling Operation.
pub trait Op: Downcast + Verify + Stringable {
    /// Get the underlying IR Operation
    fn get_operation(&self) -> Ptr<Operation>;
    /// Create a new Op object, given the containing operation.
    fn new(op: Ptr<Operation>) -> Self
    where
        Self: Sized;
}
impl_downcast!(Op);
