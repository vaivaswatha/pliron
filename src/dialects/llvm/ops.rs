use intertrait::cast_to;

use crate::{
    common_traits::{DisplayWithContext, Verify},
    context::Context,
    declare_op,
    dialect::Dialect,
    dialects::builtin::op_interfaces::IsTerminatorInterface,
    error::CompilerError,
    op::Op,
    with_context::AttachContext,
};

declare_op!(
    /// Equivalent to LLVM's return opcode.
    ///
    /// Operands:
    ///
    /// | operand | description |
    /// |-----|-------|
    /// | `arg` | any type |
    ReturnOp,
    "return",
    "llvm"
);

impl AttachContext for ReturnOp {}
impl DisplayWithContext for ReturnOp {
    fn fmt(&self, _ctx: &Context, _f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        todo!()
    }
}

impl Verify for ReturnOp {
    fn verify(&self, _ctx: &Context) -> Result<(), CompilerError> {
        todo!()
    }
}

#[cast_to]
impl IsTerminatorInterface for ReturnOp {}

pub fn register(ctx: &mut Context, dialect: &mut Dialect) {
    ReturnOp::register(ctx, dialect);
}
