use crate::{
    common_traits::{DisplayWithContext, Verify},
    context::Context,
    declare_op,
    dialect::Dialect,
    error::CompilerError,
    op::Op,
    with_context::AttachContext,
};

declare_op!(
    /// Represents a module. See MLIR's
    /// [builtin.module](https://mlir.llvm.org/docs/Dialects/Builtin/#builtinmodule-mlirmoduleop).
    ModuleOp,
    "module",
    "builtin"
);

impl AttachContext for ModuleOp {}
impl DisplayWithContext for ModuleOp {
    fn fmt(&self, _ctx: &Context, _f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        todo!()
    }
}

impl Verify for ModuleOp {
    fn verify(&self, _ctx: &Context) -> Result<(), CompilerError> {
        todo!()
    }
}

pub fn register(ctx: &mut Context, dialect: &mut Dialect) {
    ModuleOp::register(ctx, dialect);
}
