use crate::{
    common_traits::{DisplayWithContext, Verify},
    context::Context,
    declare_op,
    dialect::Dialect,
    dialects::builtin::op_traits::IsTerminator,
    error::CompilerError,
    op::Op,
    with_context::AttachContext,
};

declare_op!(
    /// Equivalent to LLVM's return opcode.
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

impl IsTerminator for ReturnOp {
    fn is_terminator(&self) -> bool {
        true
    }
}

pub fn register(ctx: &mut Context, dialect: &mut Dialect) {
    ReturnOp::register(ctx, dialect);
}
