use crate::op::Op;

/// A property to check if an Op is a terminator.
pub trait IsTerminator: Op {
    /// Is this Op a terminator?
    fn is_terminator(&self) -> bool;
}

/// By default, an Op isn't a terminator. Terminator Ops must override.
impl<T: Op> IsTerminator for T {
    default fn is_terminator(&self) -> bool {
        false
    }
}
