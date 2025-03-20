//! [Op]s defined in the LLVM dialect

use pliron::{
    arg_err_noloc,
    attribute::{AttrObj, attr_cast},
    basic_block::BasicBlock,
    builtin::{
        attr_interfaces::TypedAttrInterface,
        attributes::{FloatAttr, IdentifierAttr, IntegerAttr, TypeAttr},
        op_interfaces::{
            self, ATTR_KEY_CALLEE_TYPE, BranchOpInterface, CallOpCallable, CallOpInterface,
            IsTerminatorInterface, OneOpdInterface, OneResultInterface, SameOperandsAndResultType,
            SameOperandsType, SameResultsType, ZeroOpdInterface, ZeroResultInterface,
        },
        types::{FunctionType, IntegerType, Signedness},
    },
    common_traits::{Named, Verify},
    context::{Context, Ptr},
    derive::{format, format_op},
    identifier::Identifier,
    impl_canonical_syntax, impl_verify_succ, input_err,
    irfmt::{
        self,
        parsers::{
            block_opd_parser, delimited_list_parser, process_parsed_ssa_defs, spaced,
            ssa_opd_parser,
        },
        printers::iter_with_sep,
    },
    location::{Located, Location},
    op::{Op, OpObj},
    operation::Operation,
    parsable::{IntoParseResult, Parsable, ParseResult, StateStream},
    printable::Printable,
    result::{Error, ErrorKind, Result},
    r#type::{TypeObj, TypePtr},
    utils::vec_exns::VecExtns,
    value::Value,
    verify_err,
};

use crate::{
    attributes::InsertExtractValueIndicesAttr,
    op_interfaces::{
        BinArithOp, CastOpInterface, IntBinArithOp, IntBinArithOpWithOverflowFlag,
        PointerTypeResult,
    },
    types::{ArrayType, StructType},
};

use combine::parser::Parser;
use pliron::derive::{def_op, derive_op_interface_impl, op_interface_impl};
use thiserror::Error;

use super::{
    attributes::{GepIndexAttr, GepIndicesAttr, ICmpPredicateAttr},
    types::PointerType,
};

/// Equivalent to LLVM's return opcode.
///
/// Operands:
///
/// | operand | description |
/// |-----|-------|
/// | `arg` | any type |
#[def_op("llvm.return")]
#[format_op("operands(CharSpace(`,`))")]
#[derive_op_interface_impl(IsTerminatorInterface)]
pub struct ReturnOp;
impl ReturnOp {
    /// Create a new [ReturnOp]
    pub fn new(ctx: &mut Context, value: Option<Value>) -> Self {
        let op = Operation::new(
            ctx,
            Self::get_opid_static(),
            vec![],
            value.into_iter().collect(),
            vec![],
            0,
        );
        ReturnOp { op }
    }

    /// Get the returned value, if it exists.
    pub fn retval(&self, ctx: &Context) -> Option<Value> {
        let op = &*self.get_operation().deref(ctx);
        if op.get_num_operands() == 1 {
            Some(op.get_operand(0))
        } else {
            None
        }
    }
}
impl_verify_succ!(ReturnOp);

macro_rules! new_int_bin_op_without_format {
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
        #[pliron::derive::derive_op_interface_impl(
            OneResultInterface, SameOperandsType, SameResultsType,
            SameOperandsAndResultType, BinArithOp, IntBinArithOp
        )]
        pub struct $op_name;

        impl_verify_succ!($op_name);
    }
}

macro_rules! new_int_bin_op {
    (   $(#[$outer:meta])*
        $op_name:ident, $op_id:literal
    ) => {
        new_int_bin_op_without_format!(
            $(#[$outer])*
            #[format_op("$0 `, ` $1 ` : ` type($0)")]
            $op_name,
            $op_id
        );
    }
}

macro_rules! new_int_bin_op_with_overflow {
    (   $(#[$outer:meta])*
        $op_name:ident, $op_id:literal
    ) => {
        new_int_bin_op_without_format!(
            $(#[$outer])*
            /// ### Attributes:
            ///
            /// | key | value | via Interface |
            /// |-----|-------| --------------
            /// | [ATTR_KEY_INTEGER_OVERFLOW_FLAGS](super::op_interfaces::ATTR_KEY_INTEGER_OVERFLOW_FLAGS) | [IntegerOverflowFlagsAttr](super::attributes::IntegerOverflowFlagsAttr) | [IntBinArithOpWithOverflowFlag] |
            #[format_op("$0 `, ` $1 ` <` attr($llvm_integer_overflow_flags, `super::attributes::IntegerOverflowFlagsAttr`) `>` `: ` type($0)")]
            $op_name,
            $op_id
        );
        #[pliron::derive::op_interface_impl]
        impl IntBinArithOpWithOverflowFlag for $op_name {}
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
    #[error("Missing or incorrect predicate attribute")]
    PredAttrErr,
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
/// | [ATTR_KEY_PREDICATE](icmp_op::ATTR_KEY_PREDICATE) | [ICmpPredicateAttr](ICmpPredicateAttr) | N/A |
#[def_op("llvm.icmp")]
#[format_op("$0 ` <` attr($llvm_icmp_predicate, $ICmpPredicateAttr) `> ` $1 ` : ` type($0)")]
#[derive_op_interface_impl(SameOperandsType, OneResultInterface)]
pub struct ICmpOp;

pub mod icmp_op {
    use std::sync::LazyLock;

    use super::*;

    pub static ATTR_KEY_PREDICATE: LazyLock<Identifier> =
        LazyLock::new(|| "llvm_icmp_predicate".try_into().unwrap());
}

impl ICmpOp {
    /// Create a new [ICmpOp]
    pub fn new(ctx: &mut Context, pred: ICmpPredicateAttr, lhs: Value, rhs: Value) -> Self {
        let bool_ty = IntegerType::get(ctx, 1, Signedness::Signless);
        let op = Operation::new(
            ctx,
            Self::get_opid_static(),
            vec![bool_ty.into()],
            vec![lhs, rhs],
            vec![],
            0,
        );
        op.deref_mut(ctx)
            .attributes
            .set(icmp_op::ATTR_KEY_PREDICATE.clone(), pred);
        ICmpOp { op }
    }

    /// Get the predicate
    pub fn predicate(&self, ctx: &Context) -> ICmpPredicateAttr {
        self.get_operation()
            .deref(ctx)
            .attributes
            .get::<ICmpPredicateAttr>(&icmp_op::ATTR_KEY_PREDICATE)
            .unwrap()
            .clone()
    }
}

impl Verify for ICmpOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let loc = self.loc(ctx);
        let op = &*self.op.deref(ctx);

        if op
            .attributes
            .get::<ICmpPredicateAttr>(&icmp_op::ATTR_KEY_PREDICATE)
            .is_none()
        {
            verify_err!(op.loc(), ICmpOpVerifyErr::PredAttrErr)?
        }

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

#[derive(Error, Debug)]
pub enum AllocaOpVerifyErr {
    #[error("Operand must be a signless integer")]
    OperandType,
    #[error("Missing or incorrect type of attribute for element type")]
    ElemTypeAttr,
}

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
/// | `res` | [PointerType] |
///
/// ### Attributes:
///
/// | key | value | via Interface |
/// |-----|-------| --------------|
/// | [ATTR_KEY_ELEM_TYPE](alloca_op::ATTR_KEY_ELEM_TYPE) | [TypeAttr](pliron::builtin::attributes::TypeAttr) | N/A |
#[def_op("llvm.alloca")]
#[format_op("`[` attr($llvm_alloca_element_type, $TypeAttr) ` x ` $0 `]` ` : ` type($0)")]
#[derive_op_interface_impl(OneResultInterface, OneOpdInterface)]
pub struct AllocaOp;
impl Verify for AllocaOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let loc = self.loc(ctx);
        // Ensure correctness of operand type.
        if !self.operand_type(ctx).deref(ctx).is::<IntegerType>() {
            return verify_err!(loc, AllocaOpVerifyErr::OperandType);
        }
        let op = &*self.op.deref(ctx);
        // Ensure correctness of element type.
        if op
            .attributes
            .get::<TypeAttr>(&alloca_op::ATTR_KEY_ELEM_TYPE)
            .is_none()
        {
            verify_err!(op.loc(), AllocaOpVerifyErr::ElemTypeAttr)?
        }

        Ok(())
    }
}

#[op_interface_impl]
impl PointerTypeResult for AllocaOp {
    fn result_pointee_type(&self, ctx: &Context) -> Ptr<TypeObj> {
        self.op
            .deref(ctx)
            .attributes
            .get::<TypeAttr>(&alloca_op::ATTR_KEY_ELEM_TYPE)
            .expect("AllocaOp missing or incorrect type for elem_type attribute")
            .get_type()
    }
}

pub mod alloca_op {
    use std::sync::LazyLock;

    use super::*;
    pub static ATTR_KEY_ELEM_TYPE: LazyLock<Identifier> =
        LazyLock::new(|| "llvm_alloca_element_type".try_into().unwrap());
}

impl AllocaOp {
    /// Create a new [AllocaOp]
    pub fn new(ctx: &mut Context, elem_type: Ptr<TypeObj>, size: Value) -> Self {
        let ptr_ty = PointerType::get(ctx).into();
        let op = Operation::new(
            ctx,
            Self::get_opid_static(),
            vec![ptr_ty],
            vec![size],
            vec![],
            0,
        );
        op.deref_mut(ctx).attributes.set(
            alloca_op::ATTR_KEY_ELEM_TYPE.clone(),
            TypeAttr::new(elem_type),
        );
        AllocaOp { op }
    }
}

// Equivalent to LLVM's Bitcast opcode.
/// ### Operands
/// | operand | description |
/// |-----|-------|
/// | `arg` | non-aggregate LLVM type |
///
/// ### Result(s):
///
/// | result | description |
/// |-----|-------|
/// | `res` | non-aggregate LLVM type |
#[def_op("llvm.bitcast")]
#[format_op("$0 ` : ` type($0)")]
#[derive_op_interface_impl(OneResultInterface, OneOpdInterface)]
pub struct BitcastOp;
impl_verify_succ!(BitcastOp);

impl BitcastOp {
    /// Create a new [BitcastOp].
    pub fn new(ctx: &mut Context, res_ty: Ptr<TypeObj>, arg: Value) -> Self {
        BitcastOp {
            op: Operation::new(
                ctx,
                Self::get_opid_static(),
                vec![res_ty],
                vec![arg],
                vec![],
                0,
            ),
        }
    }
}

// Equivalent to LLVM's Unconditional Branch.
/// ### Operands
/// | operand | description |
/// |-----|-------|
/// | `dest_opds` | Any number of operands with any LLVM type |
///
/// ### Successors:
///
/// | Successor | description |
/// |-----|-------|
/// | `dest` | Any successor |
#[def_op("llvm.br")]
#[format_op("succ($0) `(` operands(CharSpace(`,`)) `)`")]
#[derive_op_interface_impl(IsTerminatorInterface, ZeroResultInterface)]
pub struct BrOp;
impl_verify_succ!(BrOp);

#[op_interface_impl]
impl BranchOpInterface for BrOp {
    fn successor_operands(&self, ctx: &Context, succ_idx: usize) -> Vec<Value> {
        assert!(succ_idx == 0, "BrOp has exactly one successor");
        self.get_operation().deref(ctx).operands().collect()
    }
}

impl BrOp {
    /// Create anew [BrOp].
    pub fn new(ctx: &mut Context, dest: Ptr<BasicBlock>, dest_opds: Vec<Value>) -> Self {
        BrOp {
            op: Operation::new(
                ctx,
                Self::get_opid_static(),
                vec![],
                dest_opds,
                vec![dest],
                0,
            ),
        }
    }
}

// Equivalent to LLVM's Conditional Branch.
/// ### Operands
/// | operand | description |
/// |-----|-------|
/// | `condition` | 1-bit signless integer |
/// | `true_dest_opds` | Any number of operands with any LLVM type |
/// | `false_dest_opds` | Any number of operands with any LLVM type |
///
/// ### Successors:
///
/// | Successor | description |
/// |-----|-------|
/// | `true_dest` | Any successor |
/// | `false_dest` | Any successor |
#[def_op("llvm.cond_br")]
#[derive_op_interface_impl(IsTerminatorInterface, ZeroResultInterface)]
pub struct CondBrOp;
impl CondBrOp {
    /// Create anew [CondBrOp].
    pub fn new(
        ctx: &mut Context,
        condition: Value,
        true_dest: Ptr<BasicBlock>,
        mut true_dest_opds: Vec<Value>,
        false_dest: Ptr<BasicBlock>,
        mut false_dest_opds: Vec<Value>,
    ) -> Self {
        let mut operands = vec![condition];
        operands.append(&mut true_dest_opds);
        operands.append(&mut false_dest_opds);
        CondBrOp {
            op: Operation::new(
                ctx,
                Self::get_opid_static(),
                vec![],
                operands,
                vec![true_dest, false_dest],
                0,
            ),
        }
    }

    /// Get the condition value for the branch.
    pub fn condition(&self, ctx: &Context) -> Value {
        self.op.deref(ctx).get_operand(0)
    }
}

impl Printable for CondBrOp {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &pliron::printable::State,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        let op = self.get_operation().deref(ctx);
        let condition = op.get_operand(0);
        let true_dest_opds = self.successor_operands(ctx, 0);
        let false_dest_opds = self.successor_operands(ctx, 1);
        let res = write!(
            f,
            "{} if {} ^{}({}) else ^{}({})",
            op.get_opid(),
            condition.disp(ctx),
            op.get_successor(0).deref(ctx).unique_name(ctx),
            iter_with_sep(
                true_dest_opds.iter(),
                pliron::printable::ListSeparator::CharSpace(',')
            )
            .disp(ctx),
            op.get_successor(1).deref(ctx).unique_name(ctx),
            iter_with_sep(
                false_dest_opds.iter(),
                pliron::printable::ListSeparator::CharSpace(',')
            )
            .disp(ctx),
        );
        res
    }
}

impl Parsable for CondBrOp {
    type Arg = Vec<(Identifier, Location)>;
    type Parsed = OpObj;
    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        results: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        if !results.is_empty() {
            input_err!(
                state_stream.loc(),
                op_interfaces::ZeroResultVerifyErr(Self::get_opid_static().to_string())
            )?
        }

        // Parse the condition operand.
        let r#if = irfmt::parsers::spaced::<StateStream, _>(combine::parser::char::string("if"));

        let condition = ssa_opd_parser();

        let true_operands = delimited_list_parser('(', ')', ',', ssa_opd_parser());

        let r_else =
            irfmt::parsers::spaced::<StateStream, _>(combine::parser::char::string("else"));

        let false_operands = delimited_list_parser('(', ')', ',', ssa_opd_parser());

        let final_parser = r#if
            .with(spaced(condition))
            .and(spaced(block_opd_parser()))
            .and(true_operands)
            .and(spaced(r_else).with(spaced(block_opd_parser()).and(false_operands)));

        final_parser
            .then(
                move |(((condition, true_dest), true_dest_opds), (false_dest, false_dest_opds))| {
                    let results = results.clone();
                    let mut operands = vec![condition];
                    operands.extend(true_dest_opds);
                    operands.extend(false_dest_opds);
                    combine::parser(move |parsable_state: &mut StateStream<'a>| {
                        let ctx = &mut parsable_state.state.ctx;
                        let op = Operation::new(
                            ctx,
                            Self::get_opid_static(),
                            vec![],
                            operands.clone(),
                            vec![true_dest, false_dest],
                            0,
                        );

                        process_parsed_ssa_defs(parsable_state, &results, op)?;
                        let op: OpObj = Box::new(CondBrOp { op });
                        Ok(op).into_parse_result()
                    })
                },
            )
            .parse_stream(state_stream)
            .into()
    }
}

impl_verify_succ!(CondBrOp);

#[op_interface_impl]
impl BranchOpInterface for CondBrOp {
    fn successor_operands(&self, ctx: &Context, succ_idx: usize) -> Vec<Value> {
        assert!(
            succ_idx == 0 || succ_idx == 1,
            "CondBrOp has exactly two successors"
        );
        let num_opds_succ0 = self
            .get_operation()
            .deref(ctx)
            .get_successor(0)
            .deref(ctx)
            .get_num_arguments();
        if succ_idx == 0 {
            // Skip `condition` operand and take num_opds_succ0 operands after that.
            self.get_operation()
                .deref(ctx)
                .operands()
                .skip(1)
                .take(num_opds_succ0)
                .collect()
        } else {
            // Skip `condition` and `true_dest_opds`. Take the remaining.
            self.get_operation()
                .deref(ctx)
                .operands()
                .skip(1 + num_opds_succ0)
                .collect()
        }
    }
}

/// A way to express whether a GEP index is a constant or an SSA value
#[derive(Clone)]
pub enum GepIndex {
    Constant(u32),
    Value(Value),
}

#[derive(Error, Debug)]
pub enum GetElementPtrOpErr {
    #[error("GetElementPtrOp has no or incorrect indices attribute")]
    IndicesAttrErr,
    #[error("The indices on this GEP are invalid for its source element type")]
    IndicesErr,
}

// Equivalent to LLVM's GetElementPtr.
/// ### Attributes:
///
/// | key | value | via Interface |
/// |-----|-------| --------------|
/// | [ATTR_KEY_INDICES](gep_op::ATTR_KEY_INDICES) | [GepIndicesAttr](super::attributes::GepIndicesAttr)> | N/A |
/// | [ATTR_KEY_SRC_ELEM_TYPE](gep_op::ATTR_KEY_SRC_ELEM_TYPE) | [TypeAttr] | N/A |
///
/// ### Operands
/// | operand | description |
/// |-----|-------|
/// | `base` | LLVM pointer type |
/// | `dynamicIndices` | Any number of signless integers |
///
/// ### Result(s):
///
/// | result | description |
/// |-----|-------|
/// | `res` | LLVM pointer type |
#[def_op("llvm.gep")]
#[format_op(
    "`<` attr($llvm_gep_src_elem_type, $TypeAttr) `>` ` (` operands(CharSpace(`,`)) `)` attr($llvm_gep_indices, $GepIndicesAttr) ` : ` type($0)"
)]
#[derive_op_interface_impl(OneResultInterface)]
pub struct GetElementPtrOp;

#[op_interface_impl]
impl PointerTypeResult for GetElementPtrOp {
    fn result_pointee_type(&self, ctx: &Context) -> Ptr<TypeObj> {
        Self::indexed_type(ctx, self.src_elem_type(ctx), &self.indices(ctx))
            .expect("Invalid indices for GEP")
    }
}

impl Verify for GetElementPtrOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let op = &*self.op.deref(ctx);
        // Ensure that we have the indices as an attribute.
        if op
            .attributes
            .get::<GepIndicesAttr>(&gep_op::ATTR_KEY_INDICES)
            .is_none()
        {
            verify_err!(op.loc(), GetElementPtrOpErr::IndicesAttrErr)?
        }

        if let Err(e @ Error { .. }) =
            Self::indexed_type(ctx, self.src_elem_type(ctx), &self.indices(ctx))
        {
            return Err(Error {
                kind: ErrorKind::VerificationFailed,
                // We reset the error origin to be from here
                backtrace: std::backtrace::Backtrace::capture(),
                ..e
            });
        }

        Ok(())
    }
}

pub mod gep_op {
    use std::sync::LazyLock;

    use super::*;
    /// [Attribute](pliron::attribute::Attribute) to get the indices vector.
    pub static ATTR_KEY_INDICES: LazyLock<Identifier> =
        LazyLock::new(|| "llvm_gep_indices".try_into().unwrap());
    /// [Attribute](pliron::attribute::Attribute) to get the source element type.
    pub static ATTR_KEY_SRC_ELEM_TYPE: LazyLock<Identifier> =
        LazyLock::new(|| "llvm_gep_src_elem_type".try_into().unwrap());
}

impl GetElementPtrOp {
    /// Create a new [GetElementPtrOp]
    pub fn new(
        ctx: &mut Context,
        base: Value,
        indices: Vec<GepIndex>,
        src_elem_type: Ptr<TypeObj>,
    ) -> Result<Self> {
        let result_type = PointerType::get(ctx).into();
        let mut attr: Vec<GepIndexAttr> = Vec::new();
        let mut opds: Vec<Value> = vec![base];
        for idx in indices {
            match idx {
                GepIndex::Constant(c) => {
                    attr.push(GepIndexAttr::Constant(c));
                }
                GepIndex::Value(v) => {
                    attr.push(GepIndexAttr::OperandIdx(opds.push_back(v)));
                }
            }
        }
        let op = Operation::new(
            ctx,
            Self::get_opid_static(),
            vec![result_type],
            opds,
            vec![],
            0,
        );
        let src_elem_type = TypeAttr::new(src_elem_type);
        op.deref_mut(ctx)
            .attributes
            .set(gep_op::ATTR_KEY_INDICES.clone(), GepIndicesAttr(attr));
        op.deref_mut(ctx)
            .attributes
            .set(gep_op::ATTR_KEY_SRC_ELEM_TYPE.clone(), src_elem_type);
        Ok(GetElementPtrOp { op })
    }

    /// Get the source pointer's element type.
    pub fn src_elem_type(&self, ctx: &Context) -> Ptr<TypeObj> {
        self.op
            .deref(ctx)
            .attributes
            .get::<TypeAttr>(&gep_op::ATTR_KEY_SRC_ELEM_TYPE)
            .expect("GetElementPtrOp missing or has incorrect src_elem_type attribute type")
            .get_type()
    }

    /// Get the base (source) pointer of this GEP.
    pub fn src_ptr(&self, ctx: &Context) -> Value {
        self.get_operation().deref(ctx).get_operand(0)
    }

    /// Get the indices of this GEP.
    pub fn indices(&self, ctx: &Context) -> Vec<GepIndex> {
        let op = &*self.op.deref(ctx);
        op.attributes
            .get::<GepIndicesAttr>(&gep_op::ATTR_KEY_INDICES)
            .unwrap()
            .0
            .iter()
            .map(|index| match index {
                GepIndexAttr::Constant(c) => GepIndex::Constant(*c),
                GepIndexAttr::OperandIdx(i) => GepIndex::Value(op.get_operand(*i)),
            })
            .collect()
    }

    /// Returns the result element type of a GEP with the given source element type and indexes.
    /// See [getIndexedType](https://llvm.org/doxygen/classllvm_1_1GetElementPtrInst.html#a99d4bfe49182f8d80abb1960f2c12d46)
    pub fn indexed_type(
        ctx: &Context,
        src_elem_type: Ptr<TypeObj>,
        indices: &[GepIndex],
    ) -> Result<Ptr<TypeObj>> {
        fn indexed_type_inner(
            ctx: &Context,
            src_elem_type: Ptr<TypeObj>,
            mut idx_itr: impl Iterator<Item = GepIndex>,
        ) -> Result<Ptr<TypeObj>> {
            let Some(idx) = idx_itr.next() else {
                return Ok(src_elem_type);
            };
            let src_elem_type = &*src_elem_type.deref(ctx);
            if let Some(st) = src_elem_type.downcast_ref::<StructType>() {
                let GepIndex::Constant(i) = idx else {
                    return arg_err_noloc!(GetElementPtrOpErr::IndicesErr);
                };
                if st.is_opaque() || i as usize >= st.num_fields() {
                    return arg_err_noloc!(GetElementPtrOpErr::IndicesErr);
                }
                indexed_type_inner(ctx, st.field_type(i as usize), idx_itr)
            } else if let Some(at) = src_elem_type.downcast_ref::<ArrayType>() {
                indexed_type_inner(ctx, at.elem_type(), idx_itr)
            } else {
                arg_err_noloc!(GetElementPtrOpErr::IndicesErr)
            }
        }
        // The first index is for the base (source) pointer. Skip that.
        indexed_type_inner(ctx, src_elem_type, indices.iter().skip(1).cloned())
    }
}

#[derive(Error, Debug)]
pub enum LoadOpVerifyErr {
    #[error("Load operand must be a pointer")]
    OperandTypeErr,
}

/// Equivalent to LLVM's Load opcode.
/// ### Operands
/// | operand | description |
/// |-----|-------|
/// | `addr` | [PointerType] |
///
/// ### Result(s):
///
/// | result | description |
/// |-----|-------|
/// | `res` | sized LLVM type |
///
/// ### Attributes:
///
#[def_op("llvm.load")]
#[format_op("$0 ` : ` type($0)")]
#[derive_op_interface_impl(OneResultInterface, OneOpdInterface)]
pub struct LoadOp;
impl LoadOp {
    /// Create a new [LoadOp]
    pub fn new(ctx: &mut Context, ptr: Value, res_ty: Ptr<TypeObj>) -> Self {
        LoadOp {
            op: Operation::new(
                ctx,
                Self::get_opid_static(),
                vec![res_ty],
                vec![ptr],
                vec![],
                0,
            ),
        }
    }
}

impl Verify for LoadOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let loc = self.loc(ctx);
        // Ensure correctness of operand type.
        if !self.operand_type(ctx).deref(ctx).is::<PointerType>() {
            return verify_err!(loc, LoadOpVerifyErr::OperandTypeErr);
        }
        Ok(())
    }
}

#[derive(Error, Debug)]
pub enum StoreOpVerifyErr {
    #[error("Store operand must have two operands")]
    NumOpdsErr,
    #[error("Store operand must have a pointer as its second argument")]
    AddrOpdTypeErr,
}

/// Equivalent to LLVM's Store opcode.
/// ### Operands
/// | operand | description |
/// |-----|-------|
/// | `addr` | [PointerType] |
/// | `value` | Sized type |
///
/// ### Attributes:
///
#[def_op("llvm.store")]
#[format_op("`*` $1 ` <- ` $0")]
#[derive_op_interface_impl(ZeroResultInterface)]
pub struct StoreOp;
impl StoreOp {
    /// Create a new [StoreOp]
    pub fn new(ctx: &mut Context, value: Value, ptr: Value) -> Self {
        StoreOp {
            op: Operation::new(
                ctx,
                Self::get_opid_static(),
                vec![],
                vec![value, ptr],
                vec![],
                0,
            ),
        }
    }

    /// Get the value operand
    pub fn value_opd(&self, ctx: &Context) -> Value {
        self.op.deref(ctx).get_operand(0)
    }

    /// Get the address operand
    pub fn address_opd(&self, ctx: &Context) -> Value {
        self.op.deref(ctx).get_operand(1)
    }
}

impl Verify for StoreOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let loc = self.loc(ctx);
        let op = &*self.op.deref(ctx);

        if op.get_num_operands() != 2 {
            return verify_err!(loc, StoreOpVerifyErr::NumOpdsErr);
        }

        use pliron::r#type::Typed;
        // Ensure correctness of the address operand.
        if !op
            .get_operand(1)
            .get_type(ctx)
            .deref(ctx)
            .is::<PointerType>()
        {
            return verify_err!(loc, StoreOpVerifyErr::AddrOpdTypeErr);
        }
        Ok(())
    }
}

/// Equivalent to LLVM's Store opcode.
/// ### Operands
/// | operand | description |
/// |-----|-------|
/// | `callee_operands` | Optional function pointer followed by any number of parameters |
///
////// ### Result(s):
///
/// | result | description |
/// |-----|-------|
/// | `res` | LLVM type |
///
/// ### Attributes:
/// | key | value | via Interface |
/// |-----|-------| --------------|
/// | [ATTR_KEY_CALLEE](call_op::ATTR_KEY_CALLEE) | [IdentifierAttr] | N/A |
/// | [ATTR_KEY_CALLEE_TYPE](pliron::builtin::op_interfaces::ATTR_KEY_CALLEE_TYPE) | [TypeAttr] | [CallOpInterface] |
///
#[def_op("llvm.call")]
#[derive_op_interface_impl(OneResultInterface)]
pub struct CallOp;

pub mod call_op {
    use std::sync::LazyLock;

    use super::*;
    pub static ATTR_KEY_CALLEE: LazyLock<Identifier> =
        LazyLock::new(|| "llvm_call_callee".try_into().unwrap());
}

impl CallOp {
    /// Get a new [CallOp].
    pub fn new(
        ctx: &mut Context,
        callee: CallOpCallable,
        callee_ty: TypePtr<FunctionType>,
        mut args: Vec<Value>,
    ) -> Self {
        let res_ty = callee_ty.deref(ctx).get_results()[0];
        let op = match callee {
            CallOpCallable::Direct(cval) => {
                let op =
                    Operation::new(ctx, Self::get_opid_static(), vec![res_ty], args, vec![], 0);
                op.deref_mut(ctx)
                    .attributes
                    .set(call_op::ATTR_KEY_CALLEE.clone(), IdentifierAttr::new(cval));
                op
            }
            CallOpCallable::Indirect(csym) => {
                args.insert(0, csym);
                Operation::new(ctx, Self::get_opid_static(), vec![res_ty], args, vec![], 0)
            }
        };
        op.deref_mut(ctx).attributes.set(
            ATTR_KEY_CALLEE_TYPE.clone(),
            TypeAttr::new(callee_ty.into()),
        );
        CallOp { op }
    }
}

impl CallOpInterface for CallOp {
    fn callee(&self, ctx: &Context) -> CallOpCallable {
        let op = self.op.deref(ctx);
        if let Some(callee_sym) = op
            .attributes
            .get::<IdentifierAttr>(&call_op::ATTR_KEY_CALLEE)
        {
            CallOpCallable::Direct(callee_sym.clone().into())
        } else {
            assert!(
                op.get_num_operands() > 0,
                "Indirect call must have function pointer operand"
            );
            CallOpCallable::Indirect(op.get_operand(0))
        }
    }

    fn args(&self, ctx: &Context) -> Vec<Value> {
        let op = self.op.deref(ctx);
        // If this is an indirect call, the first operand is the callee value.
        let skip = if matches!(self.callee(ctx), CallOpCallable::Direct(_)) {
            0
        } else {
            1
        };
        op.operands().skip(skip).collect()
    }
}
impl_canonical_syntax!(CallOp);
impl_verify_succ!(CallOp);

/// Undefined value of a type.
/// See MLIR's [llvm.mlir.undef](https://mlir.llvm.org/docs/Dialects/LLVM/#llvmmlirundef-llvmundefop).
///
/// Results:
///
/// | result | description |
/// |-----|-------|
/// | `result` | any type |
#[def_op("llvm.undef")]
#[derive_op_interface_impl(OneResultInterface)]
pub struct UndefOp;
impl_canonical_syntax!(UndefOp);
impl_verify_succ!(UndefOp);

impl UndefOp {
    /// Create a new [UndefOp].
    pub fn new(ctx: &mut Context, result_ty: Ptr<TypeObj>) -> Self {
        let op = Operation::new(
            ctx,
            Self::get_opid_static(),
            vec![result_ty],
            vec![],
            vec![],
            0,
        );
        UndefOp { op }
    }
}

/// Numeric constant.
/// See MLIR's [llvm.mlir.constant](https://mlir.llvm.org/docs/Dialects/LLVM/#llvmmlirconstant-llvmconstantop).
///
/// Attributes:
///
/// | key | value |
/// |-----|-------|
/// |[ATTR_KEY_VALUE](constant_op::ATTR_KEY_VALUE) | [IntegerAttr] or [FloatAttr] |
///
/// Results:
///
/// | result | description |
/// |-----|-------|
/// | `result` | any type |
#[def_op("llvm.constant")]
#[derive_op_interface_impl(ZeroOpdInterface, OneResultInterface)]
pub struct ConstantOp;

pub mod constant_op {
    use std::sync::LazyLock;

    use super::*;
    /// Attribute key for the constant value.
    pub static ATTR_KEY_VALUE: LazyLock<Identifier> =
        LazyLock::new(|| "llvm_constant_value".try_into().unwrap());
}

impl ConstantOp {
    /// Get the constant value that this Op defines.
    pub fn get_value(&self, ctx: &Context) -> AttrObj {
        let op = self.get_operation().deref(ctx);
        op.attributes
            .0
            .get(&constant_op::ATTR_KEY_VALUE)
            .unwrap()
            .clone()
    }

    /// Create a new [ConstantOp].
    pub fn new(ctx: &mut Context, value: AttrObj) -> Self {
        let result_type = attr_cast::<dyn TypedAttrInterface>(&*value)
            .expect("ConstantOp const value must provide TypedAttrInterface")
            .get_type();
        let op = Operation::new(
            ctx,
            Self::get_opid_static(),
            vec![result_type],
            vec![],
            vec![],
            0,
        );
        op.deref_mut(ctx)
            .attributes
            .0
            .insert(constant_op::ATTR_KEY_VALUE.clone(), value);
        ConstantOp { op }
    }
}

#[derive(Error, Debug)]
#[error("{}: Unexpected type", ConstantOp::get_opid_static())]
pub struct ConstantOpVerifyErr;

impl Verify for ConstantOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let loc = self.loc(ctx);
        let value = self.get_value(ctx);
        if !(value.is::<IntegerAttr>() || value.is::<FloatAttr>()) {
            return verify_err!(loc, ConstantOpVerifyErr);
        }
        Ok(())
    }
}

impl_canonical_syntax!(ConstantOp);

#[derive(Error, Debug)]
enum IntExtVerifyErr {
    #[error("Result must be an integer, wider than the operand type")]
    ResultTypeErr,
    #[error("Operand must be an integer")]
    OperandTypeErr,
}

fn integer_ext_verify(op: &Operation, ctx: &Context) -> Result<()> {
    use pliron::r#type::Typed;

    let loc = op.loc();
    let res_ty = op.get_type(0).deref(ctx);
    let opd_ty = op.get_operand(0).get_type(ctx).deref(ctx);
    let Some(res_ty) = res_ty.downcast_ref::<IntegerType>() else {
        return verify_err!(loc, IntExtVerifyErr::ResultTypeErr);
    };
    let Some(opd_ty) = opd_ty.downcast_ref::<IntegerType>() else {
        return verify_err!(loc, IntExtVerifyErr::OperandTypeErr);
    };
    if res_ty.get_width() <= opd_ty.get_width() {
        return verify_err!(loc, IntExtVerifyErr::ResultTypeErr);
    }
    Ok(())
}

/// Equivalent to LLVM's sext opcode.
/// ### Operands
/// | operand | description |
/// |-----|-------|
/// | `arg` | Signless integer |
/// ### Result(s):
/// | result | description |
/// |-----|-------|
/// | `res` | Signless integer |
#[def_op("llvm.sext")]
#[derive_op_interface_impl(CastOpInterface, OneResultInterface, OneOpdInterface)]
#[format_op("$0 ` to ` type($0)")]
pub struct SExtOp;
impl Verify for SExtOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        integer_ext_verify(&self.get_operation().deref(ctx), ctx)
    }
}

/// Equivalent to LLVM's zext opcode.
/// ### Operands
/// | operand | description |
/// |-----|-------|
/// | `arg` | Signless integer |
/// ### Result(s):
/// | result | description |
/// |-----|-------|
/// | `res` | Signless integer |
#[def_op("llvm.zext")]
#[derive_op_interface_impl(CastOpInterface, OneResultInterface, OneOpdInterface)]
#[format_op("$0 ` to ` type($0)")]
pub struct ZExtOp;

impl Verify for ZExtOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        integer_ext_verify(&self.get_operation().deref(ctx), ctx)
    }
}

/// Equivalent to LLVM's InsertValue opcode.
/// ### Operands
/// | operand | description |
/// |-----|-------|
/// | `aggregate` | LLVM aggregate type |
/// | `value` | LLVM type |
/// ### Result(s):
/// | result | description |
/// |-----|-------|
/// | `res` | LLVM aggregate type |
/// ### Attributes:
/// | key | value | via Interface |
/// |-----|-------| --------------|
/// | [ATTR_KEY_INDICES](insert_extract_value_op::ATTR_KEY_INDICES) | [InsertExtractValueIndicesAttr] | N/A |
///
#[def_op("llvm.insert_value")]
#[format_op(
    "$0 attr($llvm_insert_extract_value_indices, $InsertExtractValueIndicesAttr) `, ` $1 ` : ` type($0)"
)]
#[derive_op_interface_impl(OneResultInterface)]
pub struct InsertValueOp;

impl InsertValueOp {
    /// Create a new [InsertValueOp].
    /// `aggregate` is the aggregate type and `value` is the value to insert.
    /// `indices` is the list of indices to insert the value at.
    /// The `indices` must be valid for the given `aggregate` type.
    pub fn new(
        ctx: &mut Context,
        aggregate: Value,
        value: Value,
        indices: Vec<u32>,
    ) -> Result<Self> {
        use pliron::r#type::Typed;

        let result_type = aggregate.get_type(ctx);
        let op = Operation::new(
            ctx,
            Self::get_opid_static(),
            vec![result_type],
            vec![aggregate, value],
            vec![],
            0,
        );
        op.deref_mut(ctx).attributes.set(
            insert_extract_value_op::ATTR_KEY_INDICES.clone(),
            InsertExtractValueIndicesAttr(indices),
        );
        Ok(InsertValueOp { op })
    }

    /// Get the indices for inserting value into aggregate.
    pub fn indices(&self, ctx: &Context) -> Vec<u32> {
        self.get_operation()
            .deref(ctx)
            .attributes
            .get::<InsertExtractValueIndicesAttr>(&insert_extract_value_op::ATTR_KEY_INDICES)
            .unwrap()
            .0
            .clone()
    }
}

impl Verify for InsertValueOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let loc = self.loc(ctx);
        let op = &*self.op.deref(ctx);
        // Ensure that we have the indices as an attribute.
        if op
            .attributes
            .get::<InsertExtractValueIndicesAttr>(&insert_extract_value_op::ATTR_KEY_INDICES)
            .is_none()
        {
            verify_err!(loc.clone(), InsertExtractValueError::IndicesAttrErr)?
        }

        use pliron::r#type::Typed;

        // Check that the value we are inserting is of the correct type.
        let aggr_type = self.get_operation().deref(ctx).get_operand(0).get_type(ctx);
        let indices = self.indices(ctx);
        match ExtractValueOp::indexed_type(ctx, aggr_type, &indices) {
            Err(e @ Error { .. }) => {
                // We reset the error type and error origin to be from here
                return Err(Error {
                    kind: ErrorKind::VerificationFailed,
                    backtrace: std::backtrace::Backtrace::capture(),
                    ..e
                });
            }
            Ok(indexed_type) => {
                if indexed_type != self.get_operation().deref(ctx).get_operand(1).get_type(ctx) {
                    return verify_err!(loc, InsertExtractValueError::ValueTypeErr);
                }
            }
        }

        Ok(())
    }
}

/// Equivalent to LLVM's ExtractValue opcode.
/// ### Operands
/// | operand | description |
/// |-----|-------|
/// | `aggregate` | LLVM aggregate type |
/// ### Result(s):
/// | result | description |
/// |-----|-------|
/// | `res` | LLVM type |
/// ### Attributes:
/// | key | value | via Interface |
/// |-----|-------| --------------|
/// | [ATTR_KEY_INDICES](insert_extract_value_op::ATTR_KEY_INDICES) | [InsertExtractValueIndicesAttr] | N/A |
#[def_op("llvm.extract_value")]
#[format_op(
    "$0 attr($llvm_insert_extract_value_indices, $InsertExtractValueIndicesAttr) ` : ` type($0)"
)]
#[derive_op_interface_impl(OneResultInterface, OneOpdInterface)]
pub struct ExtractValueOp;

impl Verify for ExtractValueOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let loc = self.loc(ctx);
        let op = &*self.op.deref(ctx);
        // Ensure that we have the indices as an attribute.
        if op
            .attributes
            .get::<InsertExtractValueIndicesAttr>(&insert_extract_value_op::ATTR_KEY_INDICES)
            .is_none()
        {
            verify_err!(loc.clone(), InsertExtractValueError::IndicesAttrErr)?
        }

        use pliron::r#type::Typed;
        // Check that the result type matches the indexed type
        let aggr_type = self.get_operation().deref(ctx).get_operand(0).get_type(ctx);
        let indices = self.indices(ctx);
        match Self::indexed_type(ctx, aggr_type, &indices) {
            Err(e @ Error { .. }) => {
                // We reset the error type and error origin to be from here
                return Err(Error {
                    kind: ErrorKind::VerificationFailed,
                    backtrace: std::backtrace::Backtrace::capture(),
                    ..e
                });
            }
            Ok(indexed_type) => {
                if indexed_type != self.get_operation().deref(ctx).get_type(0) {
                    return verify_err!(loc, InsertExtractValueError::ValueTypeErr);
                }
            }
        }

        Ok(())
    }
}

impl ExtractValueOp {
    /// Create a new [ExtractValueOp].
    /// `aggregate` is the aggregate type and `indices` is the list of indices to extract the value from.
    /// The `indices` must be valid for the given `aggregate` type.
    /// The result type of the operation is the type of the value at the given indices.
    pub fn new(ctx: &mut Context, aggregate: Value, indices: Vec<u32>) -> Result<Self> {
        use pliron::r#type::Typed;
        let result_type = Self::indexed_type(ctx, aggregate.get_type(ctx), &indices)?;
        let op = Operation::new(
            ctx,
            Self::get_opid_static(),
            vec![result_type],
            vec![aggregate],
            vec![],
            0,
        );
        op.deref_mut(ctx).attributes.set(
            insert_extract_value_op::ATTR_KEY_INDICES.clone(),
            InsertExtractValueIndicesAttr(indices),
        );
        Ok(ExtractValueOp { op })
    }

    /// Get the indices for extracting value from aggregate.
    pub fn indices(&self, ctx: &Context) -> Vec<u32> {
        self.get_operation()
            .deref(ctx)
            .attributes
            .get::<InsertExtractValueIndicesAttr>(&insert_extract_value_op::ATTR_KEY_INDICES)
            .unwrap()
            .0
            .clone()
    }

    /// Returns the type of the value at the given indices in the given aggregate type.
    pub fn indexed_type(
        ctx: &Context,
        aggr_type: Ptr<TypeObj>,
        indices: &[u32],
    ) -> Result<Ptr<TypeObj>> {
        fn indexed_type_inner(
            ctx: &Context,
            aggr_type: Ptr<TypeObj>,
            mut idx_itr: impl Iterator<Item = u32>,
        ) -> Result<Ptr<TypeObj>> {
            let Some(idx) = idx_itr.next() else {
                return Ok(aggr_type);
            };
            let aggr_type = &*aggr_type.deref(ctx);
            if let Some(st) = aggr_type.downcast_ref::<StructType>() {
                if st.is_opaque() || idx as usize >= st.num_fields() {
                    return arg_err_noloc!(InsertExtractValueError::InvalidIndicesErr);
                }
                indexed_type_inner(ctx, st.field_type(idx as usize), idx_itr)
            } else if let Some(at) = aggr_type.downcast_ref::<ArrayType>() {
                if idx as u64 >= at.size() {
                    return arg_err_noloc!(InsertExtractValueError::InvalidIndicesErr);
                }
                indexed_type_inner(ctx, at.elem_type(), idx_itr)
            } else {
                arg_err_noloc!(InsertExtractValueError::InvalidIndicesErr)
            }
        }
        indexed_type_inner(ctx, aggr_type, indices.iter().cloned())
    }
}

#[derive(Error, Debug)]
pub enum InsertExtractValueError {
    #[error("Insert/Extract value instruction has no or incorrect indices attribute")]
    IndicesAttrErr,
    #[error("Invalid indices on insert/extract value instruction")]
    InvalidIndicesErr,
    #[error("Value being inserted / extracted does not match the type of the indexed aggregate")]
    ValueTypeErr,
}

pub mod insert_extract_value_op {
    use std::sync::LazyLock;

    use super::*;
    pub static ATTR_KEY_INDICES: LazyLock<Identifier> =
        LazyLock::new(|| "llvm_insert_extract_value_indices".try_into().unwrap());
}

/// Equivalent to LLVM's Select opcode.
/// ### Operands
/// | operand | description |
/// |-----|-------|
/// | `condition` | i1 |
/// | `true_dest` | any type |
/// | `false_dest` | any type |
/// ### Result(s):
/// | result | description |
/// |-----|-------|
/// | `res` | any type |
#[def_op("llvm.select")]
#[derive_op_interface_impl(OneResultInterface)]
#[format_op("$0 ` ? ` $1 ` : ` $2 ` : ` type($0)")]
pub struct SelectOp;

impl SelectOp {
    /// Create a new [SelectOp].
    pub fn new(ctx: &mut Context, cond: Value, true_val: Value, false_val: Value) -> Self {
        use pliron::r#type::Typed;

        let result_type = true_val.get_type(ctx);
        let op = Operation::new(
            ctx,
            Self::get_opid_static(),
            vec![result_type],
            vec![cond, true_val, false_val],
            vec![],
            0,
        );
        SelectOp { op }
    }
}

impl Verify for SelectOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        use pliron::r#type::Typed;

        let loc = self.loc(ctx);
        let op = &*self.op.deref(ctx);
        let ty = op.get_type(0);
        let cond_ty = op.get_operand(0).get_type(ctx);
        let true_ty = op.get_operand(1).get_type(ctx);
        let false_ty = op.get_operand(2).get_type(ctx);
        if ty != true_ty || ty != false_ty {
            return verify_err!(loc, SelectOpVerifyErr::ResultTypeErr);
        }

        let cond_ty = cond_ty.deref(ctx);
        let cond_ty = cond_ty.downcast_ref::<IntegerType>();
        if cond_ty.is_none_or(|ty| ty.get_width() != 1) {
            return verify_err!(loc, SelectOpVerifyErr::ConditionTypeErr);
        }
        Ok(())
    }
}

#[derive(Error, Debug)]
pub enum SelectOpVerifyErr {
    #[error("Result must be the same as the true and false destination types")]
    ResultTypeErr,
    #[error("Condition must be an i1")]
    ConditionTypeErr,
}

/// Register ops in the LLVM dialect.
pub fn register(ctx: &mut Context) {
    AddOp::register(ctx, AddOp::parser_fn);
    SubOp::register(ctx, SubOp::parser_fn);
    MulOp::register(ctx, MulOp::parser_fn);
    ShlOp::register(ctx, ShlOp::parser_fn);
    UDivOp::register(ctx, UDivOp::parser_fn);
    SDivOp::register(ctx, SDivOp::parser_fn);
    URemOp::register(ctx, URemOp::parser_fn);
    SRemOp::register(ctx, SRemOp::parser_fn);
    AndOp::register(ctx, AndOp::parser_fn);
    OrOp::register(ctx, OrOp::parser_fn);
    XorOp::register(ctx, XorOp::parser_fn);
    LShrOp::register(ctx, LShrOp::parser_fn);
    AShrOp::register(ctx, AShrOp::parser_fn);
    ICmpOp::register(ctx, ICmpOp::parser_fn);
    AllocaOp::register(ctx, AllocaOp::parser_fn);
    BitcastOp::register(ctx, BitcastOp::parser_fn);
    BrOp::register(ctx, BrOp::parser_fn);
    CondBrOp::register(ctx, CondBrOp::parser_fn);
    GetElementPtrOp::register(ctx, GetElementPtrOp::parser_fn);
    LoadOp::register(ctx, LoadOp::parser_fn);
    StoreOp::register(ctx, StoreOp::parser_fn);
    CallOp::register(ctx, CallOp::parser_fn);
    ConstantOp::register(ctx, ConstantOp::parser_fn);
    SExtOp::register(ctx, SExtOp::parser_fn);
    ZExtOp::register(ctx, ZExtOp::parser_fn);
    InsertValueOp::register(ctx, InsertValueOp::parser_fn);
    ExtractValueOp::register(ctx, ExtractValueOp::parser_fn);
    SelectOp::register(ctx, SelectOp::parser_fn);
    UndefOp::register(ctx, UndefOp::parser_fn);
    ReturnOp::register(ctx, ReturnOp::parser_fn);
}
