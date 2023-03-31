use crate::{
    attribute::{self, AttrObj},
    common_traits::{DisplayWithContext, Verify},
    context::Context,
    declare_op,
    dialect::Dialect,
    error::CompilerError,
    op::Op,
    operation::Operation,
    with_context::AttachContext,
};

use super::{attributes::IntegerAttr, types::IntegerType};

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

declare_op!(
    /// Integer constant.
    /// See MLIR's [arith.constant](https://mlir.llvm.org/docs/Dialects/ArithOps/#arithconstant-mlirarithconstantop)
    ConstantOp,
    "constant",
    "builtin"
);

impl ConstantOp {
    const VAL_ATTR_KEY: &str = "constant.value";
    /// Get the constant value that this Op defines.
    pub fn get_value(&self, ctx: &Context) -> AttrObj {
        let op = self.get_operation();
        attribute::clone::<IntegerAttr>(op.deref(ctx).attributes.get(Self::VAL_ATTR_KEY).unwrap())
    }

    /// Create a new [ConstantOp]. The underlying [Operation] is not linked to a [BasicBlock](crate::basic_block::BasicBlock).
    pub fn new_unlinked(ctx: &mut Context, value: AttrObj) -> ConstantOp {
        assert!(
            value.is::<IntegerAttr>(),
            "Expected IntegerAttr when creating ConstantOp"
        );
        let result_type = IntegerType::get(ctx, 64, super::types::Signedness::Signed);
        let op = Operation::new(ctx, Self::get_opid_static(), vec![result_type], vec![]);
        op.deref_mut(ctx)
            .attributes
            .insert(Self::VAL_ATTR_KEY, value);
        ConstantOp { op }
    }
}

impl AttachContext for ConstantOp {}
impl DisplayWithContext for ConstantOp {
    fn fmt(&self, ctx: &Context, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.get_value(ctx).with_ctx(ctx))
    }
}

impl Verify for ConstantOp {
    fn verify(&self, ctx: &Context) -> Result<(), CompilerError> {
        let value = self.get_value(ctx);
        if !value.is::<IntegerAttr>() {
            return Err(CompilerError::VerificationError {
                msg: "Unexpected constant type".to_string(),
            });
        }
        let op = &*self.get_operation().deref(ctx);
        if op.get_opid() != Self::get_opid_static() {
            return Err(CompilerError::VerificationError {
                msg: "Incorrect OpId".to_string(),
            });
        }
        if op.get_num_results() != 1 || op.get_num_operands() != 0 {
            return Err(CompilerError::VerificationError {
                msg: "Incorrect number of results or operands".to_string(),
            });
        }
        Ok(())
    }
}

pub fn register(ctx: &mut Context, dialect: &mut Dialect) {
    ModuleOp::register(ctx, dialect);
    ConstantOp::register(ctx, dialect);
}
