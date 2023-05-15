use intertrait::cast_to;

use crate::{
    common_traits::{DisplayWithContext, Verify},
    context::Context,
    declare_op,
    dialect::Dialect,
    dialects::builtin::op_interfaces::IsTerminatorInterface,
    error::CompilerError,
    op::Op,
    operation::Operation,
    use_def_lists::Value,
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

impl ReturnOp {
    pub fn new_unlinked(ctx: &mut Context, value: Value) -> ReturnOp {
        let op = Operation::new(ctx, Self::get_opid_static(), vec![], vec![value], 0);
        ReturnOp { op }
    }
}

impl AttachContext for ReturnOp {}
impl DisplayWithContext for ReturnOp {
    fn fmt(&self, ctx: &Context, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "{} {}",
            self.get_opid().with_ctx(ctx),
            self.get_operation()
                .deref(ctx)
                .get_operand_ref(0)
                .unwrap()
                .with_ctx(ctx)
        )
    }
}

impl Verify for ReturnOp {
    fn verify(&self, _ctx: &Context) -> Result<(), CompilerError> {
        Ok(())
    }
}

#[cast_to]
impl IsTerminatorInterface for ReturnOp {}

pub fn register(ctx: &mut Context, dialect: &mut Dialect) {
    ReturnOp::register(ctx, dialect);
}
