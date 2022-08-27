use crate::{context::Context, error::CompilerError};

// We can't use std::fmt::Display as we want Context.
pub trait Stringable {
    fn to_string(&self, ctx: &Context) -> String;
}

pub trait Verify {
    fn verify(&self, ctx: &Context) -> Result<(), CompilerError>;
}
