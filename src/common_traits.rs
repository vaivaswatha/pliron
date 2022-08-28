use crate::{context::Context, error::CompilerError};

/// Any object that can be converted to a user-friendly string.
/// We can't use std::fmt::Display as we may want Context.
pub trait Stringable {
    fn to_string(&self, ctx: &Context) -> String;
}

/// Check and ensure correctness.
pub trait Verify {
    fn verify(&self, ctx: &Context) -> Result<(), CompilerError>;
}
