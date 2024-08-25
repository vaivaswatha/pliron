//! [Op] Interfaces defined in the LLVM dialect.

use std::sync::LazyLock;

use pliron_derive::op_interface;
use thiserror::Error;

use pliron::{
    builtin::{
        op_interfaces::{OneResultInterface, SameOperandsAndResultType},
        types::{IntegerType, Signedness},
    },
    context::{Context, Ptr},
    identifier::Identifier,
    location::Located,
    op::{op_cast, Op},
    operation::Operation,
    r#type::{TypeObj, Typed},
    result::Result,
    value::Value,
    verify_err,
};

use super::{attributes::IntegerOverflowFlagsAttr, types::PointerType};

#[derive(Error, Debug)]
#[error("Binary Arithmetic Op must have exactly two operands and one result")]
pub struct BinArithOpErr;

/// Binary arithmetic [Op].
#[op_interface]
pub trait BinArithOp: SameOperandsAndResultType + OneResultInterface {
    /// Create a new binary arithmetic operation given the operands.
    fn new(ctx: &mut Context, lhs: Value, rhs: Value) -> Self
    where
        Self: Sized,
    {
        let op = Operation::new(
            ctx,
            Self::get_opid_static(),
            vec![lhs.get_type(ctx)],
            vec![lhs, rhs],
            vec![],
            0,
        );
        *Operation::get_op(op, ctx).downcast::<Self>().ok().unwrap()
    }

    fn verify(op: &dyn Op, ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        let op = op.get_operation().deref(ctx);
        if op.get_num_operands() != 2 {
            return verify_err!(op.loc(), BinArithOpErr);
        }

        Ok(())
    }
}

#[derive(Error, Debug)]
#[error("Integer binary arithmetic Op can only have signless integer result/operand type")]
pub struct IntBinArithOpErr;

/// Integer binary arithmetic [Op]
#[op_interface]
pub trait IntBinArithOp: BinArithOp {
    fn verify(op: &dyn Op, ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        let ty = op_cast::<dyn SameOperandsAndResultType>(op)
            .expect("Op must impl SameOperandsAndResultType")
            .get_type(ctx)
            .deref(ctx);
        let Some(int_ty) = ty.downcast_ref::<IntegerType>() else {
            return verify_err!(op.get_operation().deref(ctx).loc(), IntBinArithOpErr);
        };

        if int_ty.get_signedness() != Signedness::Signless {
            return verify_err!(op.get_operation().deref(ctx).loc(), IntBinArithOpErr);
        }

        Ok(())
    }
}

/// Attribute key for integer overflow flags.
pub static ATTR_KEY_INTEGER_OVERFLOW_FLAGS: LazyLock<Identifier> =
    LazyLock::new(|| "llvm_integer_overflow_flags".try_into().unwrap());

#[derive(Error, Debug)]
#[error("IntegerOverflowFlag missing on Op")]
pub struct IntBinArithOpWithOverflowFlagErr;

/// Integer binary arithmetic [Op] with [IntegerOverflowFlagsAttr]
#[op_interface]
pub trait IntBinArithOpWithOverflowFlag: IntBinArithOp {
    /// Get the integer overflow flag on this [Op].
    fn integer_overflow_flag(&self, ctx: &Context) -> IntegerOverflowFlagsAttr
    where
        Self: Sized,
    {
        self.get_operation()
            .deref(ctx)
            .attributes
            .get::<IntegerOverflowFlagsAttr>(&ATTR_KEY_INTEGER_OVERFLOW_FLAGS)
            .expect("Integer overflow flag missing or is of incorrect type")
            .clone()
    }

    /// Set the integer overflow flag for this [Op].
    fn set_integer_overflow_flag(&self, ctx: &Context, flag: IntegerOverflowFlagsAttr)
    where
        Self: Sized,
    {
        self.get_operation()
            .deref_mut(ctx)
            .attributes
            .set(ATTR_KEY_INTEGER_OVERFLOW_FLAGS.clone(), flag);
    }

    fn verify(op: &dyn Op, ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        let op = op.get_operation().deref(ctx);
        if op
            .attributes
            .get::<IntegerOverflowFlagsAttr>(&ATTR_KEY_INTEGER_OVERFLOW_FLAGS)
            .is_none()
        {
            return verify_err!(op.loc(), IntBinArithOpWithOverflowFlagErr);
        }

        Ok(())
    }
}

#[derive(Error, Debug)]
#[error("Result must be a pointer type, but is not")]
pub struct PointerTypeResultVerifyErr;

/// An [Op] with a single result whose type is [PointerType]
#[op_interface]
pub trait PointerTypeResult: OneResultInterface {
    /// Get the pointee type of the result pointer.
    fn result_pointee_type(&self, ctx: &Context) -> Ptr<TypeObj>;

    fn verify(op: &dyn Op, ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        if !op_cast::<dyn OneResultInterface>(op)
            .expect("An Op here must impl OneResultInterface")
            .result_type(ctx)
            .deref(ctx)
            .is::<PointerType>()
        {
            return verify_err!(
                op.get_operation().deref(ctx).loc(),
                PointerTypeResultVerifyErr
            );
        }

        Ok(())
    }
}
