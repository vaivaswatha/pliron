//! [Op]s defined in the LLVM dialect

use crate::{
    common_traits::Verify,
    context::Context,
    dialect::Dialect,
    dialects::{
        builtin::{
            op_interfaces::{
                IsTerminatorInterface, OneOpdInterface, OneResultInterface,
                SameOperandsAndResultType, SameOperandsType, SameResultsType, ZeroResultVerifyErr,
            },
            types::IntegerType,
        },
        llvm::op_interfaces::{
            BinArithOp, IntBinArithOp, IntBinArithOpWithOverflowFlag, PointerTypeResult,
        },
    },
    error::Result,
    identifier::Identifier,
    impl_canonical_syntax, impl_op_interface, impl_verify_succ, input_err,
    irfmt::parsers::ssa_opd_parser,
    location::{Located, Location},
    op::{Op, OpObj},
    operation::Operation,
    parsable::{Parsable, ParseResult},
    printable::{self, Printable},
    r#type::TypePtr,
    use_def_lists::Value,
    verify_err,
};

use combine::parser::Parser;
use pliron_derive::def_op;
use thiserror::Error;

use super::types::PointerType;

/// Equivalent to LLVM's return opcode.
///
/// Operands:
///
/// | operand | description |
/// |-----|-------|
/// | `arg` | any type |
#[def_op("llvm.return")]
pub struct ReturnOp {}

impl ReturnOp {
    pub fn new(ctx: &mut Context, value: Value) -> Self {
        let op = Operation::new(ctx, Self::get_opid_static(), vec![], vec![value], 0);
        ReturnOp { op }
    }
}

impl Printable for ReturnOp {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        write!(
            f,
            "{} {}",
            self.get_opid().disp(ctx),
            self.get_operation()
                .deref(ctx)
                .get_operand_ref(0)
                .unwrap()
                .disp(ctx)
        )
    }
}

impl_verify_succ!(ReturnOp);

impl Parsable for ReturnOp {
    type Arg = Vec<(Identifier, Location)>;
    type Parsed = OpObj;
    fn parse<'a>(
        state_stream: &mut crate::parsable::StateStream<'a>,
        results: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        if !results.is_empty() {
            input_err!(
                state_stream.loc(),
                ZeroResultVerifyErr(Self::get_opid_static().to_string())
            )?
        }

        ssa_opd_parser()
            .parse_stream(state_stream)
            .map(|opd| -> OpObj { Box::new(Self::new(state_stream.state.ctx, opd)) })
            .into()
    }
}

impl_op_interface!(IsTerminatorInterface for ReturnOp {});

macro_rules! new_int_bin_op {
    (   $(#[$outer:meta])*
        $op_name:ident, $op_id:literal
    ) => {
        #[def_op($op_id)]
        $(#[$outer])*
        /// ### Operands:
        ///
        /// | operand | description |
        /// |-----|-------|
        /// | `lhs` | Signless integer |
        /// | `rhs` | Signless integer |
        ///
        /// ### Result(s):
        ///
        /// | result | description |
        /// |-----|-------|
        /// | `res` | Signless integer |
        pub struct $op_name {}

        impl_verify_succ!($op_name);
        impl_canonical_syntax!($op_name);
        impl_op_interface!(SameOperandsType for $op_name {});
        impl_op_interface!(SameResultsType for $op_name {});
        impl_op_interface!(SameOperandsAndResultType for $op_name {});
        impl_op_interface!(BinArithOp for $op_name {});
        impl_op_interface!(IntBinArithOp for $op_name {});
    }
}

macro_rules! new_int_bin_op_with_overflow {
    (   $(#[$outer:meta])*
        $op_name:ident, $op_id:literal
    ) => {
        new_int_bin_op!(
            $(#[$outer])*
            /// ### Attributes:
            ///
            /// | key | value | via Interface |
            /// |-----|-------| --------------
            /// | [ATTR_KEY_INTEGER_OVERFLOW_FLAGS](super::op_interfaces::ATTR_KEY_INTEGER_OVERFLOW_FLAGS) | [StringAttr](pliron::dialects::builtin::attributes::StringAttr) | [IntBinArithOpWithOverflowFlag] |
            $op_name,
            $op_id
        );
        impl_op_interface!(IntBinArithOpWithOverflowFlag for $op_name {});
    }
}
new_int_bin_op_with_overflow!(
    /// Equivalent to LLVM's Add opcode.
    AddOp,
    "llvm.add"
);

new_int_bin_op_with_overflow!(
    /// Equivalent to LLVM's Sub opcode.
    SubOp,
    "llvm.sub"
);

new_int_bin_op_with_overflow!(
    /// Equivalent to LLVM's Mul opcode.
    MulOp,
    "llvm.mul"
);

new_int_bin_op_with_overflow!(
    /// Equivalent to LLVM's Shl opcode.
    ShlOp,
    "llvm.shl"
);

new_int_bin_op!(
    /// Equivalent to LLVM's UDiv opcode.
    UDivOp,
    "llvm.udiv"
);

new_int_bin_op!(
    /// Equivalent to LLVM's SDiv opcode.
    SDivOp,
    "llvm.sdiv"
);

new_int_bin_op!(
    /// Equivalent to LLVM's URem opcode.
    URemOp,
    "llvm.urem"
);

new_int_bin_op!(
    /// Equivalent to LLVM's SRem opcode.
    SRemOp,
    "llvm.srem"
);

new_int_bin_op!(
    /// Equivalent to LLVM's And opcode.
    AndOp,
    "llvm.and"
);

new_int_bin_op!(
    /// Equivalent to LLVM's Or opcode.
    OrOp,
    "llvm.or"
);

new_int_bin_op!(
    /// Equivalent to LLVM's Xor opcode.
    XorOp,
    "llvm.xor"
);

new_int_bin_op!(
    /// Equivalent to LLVM's LShr opcode.
    LShrOp,
    "llvm.lshr"
);

new_int_bin_op!(
    /// Equivalent to LLVM's AShr opcode.
    AShrOp,
    "llvm.ashr"
);

#[derive(Error, Debug)]
pub enum ICmpOpVerifyErr {
    #[error("Result must be 1-bit integer (bool)")]
    ResultNotBool,
    #[error("Operand must be integer or pointer types")]
    IncorrectOperandsType,
}

/// Equivalent to LLVM's ICmp opcode.
/// ### Operands
/// | operand | description |
/// |-----|-------|
/// | `lhs` | Signless integer or pointer |
/// | `rhs` | Signless integer or pointer |
///
/// ### Result(s):
///
/// | result | description |
/// |-----|-------|
/// | `res` | 1-bit signless integer |
/// ### Attributes:
///
/// | key | value | via Interface |
/// |-----|-------| --------------|
/// | [ATTR_KEY_PREDICATE](ICmpOp::ATTR_KEY_PREDICATE) | [ICmpPredicateAttr](super::attributes::ICmpPredicateAttr) | N/A |
#[def_op("llvm.icmp")]
pub struct ICmpOp {}

impl ICmpOp {
    pub const ATTR_KEY_PREDICATE: &'static str = "llvm.icmp_predicate";
}

impl Verify for ICmpOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let loc = self.get_operation().deref(ctx).loc();
        let res_ty: TypePtr<IntegerType> =
            TypePtr::from_ptr(self.result_type(ctx), ctx).map_err(|mut err| {
                err.set_loc(loc.clone());
                err
            })?;

        if res_ty.deref(ctx).get_width() != 1 {
            return verify_err!(loc, ICmpOpVerifyErr::ResultNotBool);
        }

        let opd_ty = self.operand_type(ctx).deref(ctx);
        if !(opd_ty.is::<IntegerType>() || opd_ty.is::<PointerType>()) {
            return verify_err!(loc, ICmpOpVerifyErr::IncorrectOperandsType);
        }

        Ok(())
    }
}
impl_canonical_syntax!(ICmpOp);
impl_op_interface!(SameOperandsType for ICmpOp {});
impl_op_interface!(OneResultInterface for ICmpOp {});

#[derive(Error, Debug)]
#[error("Operand must be a signless integer")]
pub struct AllocaOpVerifyErr;

/// Equivalent to LLVM's Alloca opcode.
/// ### Operands
/// | operand | description |
/// |-----|-------|
/// | `array_size` | Signless integer |
///
/// ### Result(s):
///
/// | result | description |
/// |-----|-------|
/// | `res` | LLVM pointer type |
///
/// ### Attributes:
///
/// | key | value | via Interface |
/// |-----|-------| --------------|
/// | [ATTR_KEY_ELEM_TYPE](AllocaOp::ATTR_KEY_ELEM_TYPE) | [TypeAttr](pliron::dialects::builtin::attributes::TypeAttr) | N/A |
#[def_op("llvm.alloca")]
pub struct AllocaOp {}
impl_canonical_syntax!(AllocaOp);
impl Verify for AllocaOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let loc = self.get_operation().deref(ctx).loc();
        if !self.operand_type(ctx).deref(ctx).is::<IntegerType>() {
            return verify_err!(loc, AllocaOpVerifyErr);
        }

        Ok(())
    }
}
impl_op_interface!(OneResultInterface for AllocaOp {});
impl_op_interface!(OneOpdInterface for AllocaOp {});
impl_op_interface!(PointerTypeResult for AllocaOp {});
impl AllocaOp {
    pub const ATTR_KEY_ELEM_TYPE: &'static str = "llvm.element_type";
}

/// Register ops in the LLVM dialect.
pub fn register(ctx: &mut Context, dialect: &mut Dialect) {
    AddOp::register(ctx, dialect, AddOp::parser_fn);
    SubOp::register(ctx, dialect, SubOp::parser_fn);
    MulOp::register(ctx, dialect, MulOp::parser_fn);
    ShlOp::register(ctx, dialect, ShlOp::parser_fn);
    UDivOp::register(ctx, dialect, UDivOp::parser_fn);
    SDivOp::register(ctx, dialect, SDivOp::parser_fn);
    URemOp::register(ctx, dialect, URemOp::parser_fn);
    SRemOp::register(ctx, dialect, SRemOp::parser_fn);
    AndOp::register(ctx, dialect, AndOp::parser_fn);
    OrOp::register(ctx, dialect, OrOp::parser_fn);
    XorOp::register(ctx, dialect, XorOp::parser_fn);
    LShrOp::register(ctx, dialect, LShrOp::parser_fn);
    AShrOp::register(ctx, dialect, AShrOp::parser_fn);
    ICmpOp::register(ctx, dialect, ICmpOp::parser_fn);
    AllocaOp::register(ctx, dialect, AllocaOp::parser_fn);

    ReturnOp::register(ctx, dialect, ReturnOp::parser_fn);
}
