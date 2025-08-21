//! [Op]s defined in the LLVM dialect

use std::vec;

use pliron::{
    arg_err_noloc,
    attribute::{AttrObj, attr_cast},
    basic_block::BasicBlock,
    builtin::{
        attr_interfaces::TypedAttrInterface,
        attributes::{IdentifierAttr, IntegerAttr, TypeAttr},
        op_interfaces::{
            self, BranchOpInterface, CallOpCallable, CallOpInterface, IsTerminatorInterface,
            IsolatedFromAboveInterface, OneOpdInterface, OneResultInterface,
            OperandSegmentInterface, SameOperandsAndResultType, SameOperandsType, SameResultsType,
            SingleBlockRegionInterface, SymbolOpInterface, SymbolUserOpInterface, ZeroOpdInterface,
            ZeroResultInterface,
        },
        ops::FuncOp,
        types::{FunctionType, IntegerType, Signedness},
    },
    common_traits::{Named, Verify},
    context::{Context, Ptr},
    derive::{derive_attr_get_set, format, format_op},
    identifier::Identifier,
    impl_verify_succ, indented_block, input_err,
    irfmt::{
        self,
        parsers::{
            attr_parser, block_opd_parser, delimited_list_parser, process_parsed_ssa_defs, spaced,
            ssa_opd_parser, type_parser,
        },
        printers::{iter_with_sep, list_with_sep},
    },
    location::{Located, Location},
    op::{Op, OpObj},
    operation::Operation,
    parsable::{IntoParseResult, Parsable, ParseResult, StateStream},
    printable::{Printable, indented_nl},
    region::Region,
    result::{Error, ErrorKind, Result},
    symbol_table::SymbolTableCollection,
    r#type::{TypeObj, TypePtr},
    utils::vec_exns::VecExtns,
    value::Value,
    verify_err,
};

use crate::{
    attributes::{CaseValuesAttr, InsertExtractValueIndicesAttr},
    op_interfaces::{
        BinArithOp, CastOpInterface, IntBinArithOp, IntBinArithOpWithOverflowFlag,
        PointerTypeResult,
    },
    types::{ArrayType, StructType},
};

use combine::{
    between,
    parser::{Parser, char::spaces},
    token,
};
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
/// ### Operand(s):
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
#[def_op("llvm.icmp")]
#[format_op("$0 ` <` attr($icmp_predicate, $ICmpPredicateAttr) `> ` $1 ` : ` type($0)")]
#[derive_op_interface_impl(SameOperandsType, OneResultInterface)]
#[derive_attr_get_set(icmp_predicate : ICmpPredicateAttr)]
pub struct ICmpOp;

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
        let op = ICmpOp { op };
        op.set_attr_icmp_predicate(ctx, pred);
        op
    }

    /// Get the predicate
    pub fn predicate(&self, ctx: &Context) -> ICmpPredicateAttr {
        self.get_attr_icmp_predicate(ctx)
            .expect("ICmpOp missing or incorrect predicate attribute type")
            .clone()
    }
}

impl Verify for ICmpOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let loc = self.loc(ctx);

        if self.get_attr_icmp_predicate(ctx).is_none() {
            verify_err!(loc.clone(), ICmpOpVerifyErr::PredAttrErr)?
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
#[def_op("llvm.alloca")]
#[format_op("`[` attr($alloca_element_type, $TypeAttr) ` x ` $0 `]` ` : ` type($0)")]
#[derive_op_interface_impl(OneResultInterface, OneOpdInterface)]
#[derive_attr_get_set(alloca_element_type : TypeAttr)]
pub struct AllocaOp;
impl Verify for AllocaOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let loc = self.loc(ctx);
        // Ensure correctness of operand type.
        if !self.operand_type(ctx).deref(ctx).is::<IntegerType>() {
            return verify_err!(loc, AllocaOpVerifyErr::OperandType);
        }
        // Ensure correctness of element type.
        if self.get_attr_alloca_element_type(ctx).is_none() {
            verify_err!(loc, AllocaOpVerifyErr::ElemTypeAttr)?
        }

        Ok(())
    }
}

#[op_interface_impl]
impl PointerTypeResult for AllocaOp {
    fn result_pointee_type(&self, ctx: &Context) -> Ptr<TypeObj> {
        self.get_attr_alloca_element_type(ctx)
            .expect("AllocaOp missing or incorrect type for elem_type attribute")
            .get_type()
    }
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
        let op = AllocaOp { op };
        op.set_attr_alloca_element_type(ctx, TypeAttr::new(elem_type));
        op
    }
}

/// Equivalent to LLVM's Bitcast opcode.
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
#[format_op("$0 ` to ` type($0)")]
#[derive_op_interface_impl(OneResultInterface, OneOpdInterface, CastOpInterface)]
pub struct BitcastOp;
impl_verify_succ!(BitcastOp);

#[derive(Error, Debug)]
pub enum IntToPtrOpErr {
    #[error("Operand must be a signless integer")]
    OperandTypeErr,
    #[error("Result must be a pointer type")]
    ResultTypeErr,
}

/// Equivalent to LLVM's IntToPtr opcode.
/// ### Operands
/// | operand | description |
/// |-----|-------|
/// | `arg` | Signless integer |
////
/// ### Result(s):
///
/// | result | description |
/// |-----|-------|
/// | `res` | [PointerType] |
///
#[def_op("llvm.inttoptr")]
#[format_op("$0 ` to ` type($0)")]
#[derive_op_interface_impl(OneResultInterface, OneOpdInterface, CastOpInterface)]
pub struct IntToPtrOp;

impl Verify for IntToPtrOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let loc = self.loc(ctx);
        // Ensure correctness of operand type.
        if !self.operand_type(ctx).deref(ctx).is::<IntegerType>() {
            return verify_err!(loc, IntToPtrOpErr::OperandTypeErr);
        }
        // Ensure correctness of result type.
        if !self.result_type(ctx).deref(ctx).is::<PointerType>() {
            return verify_err!(loc, IntToPtrOpErr::ResultTypeErr);
        }
        Ok(())
    }
}

#[derive(Error, Debug)]
pub enum PtrToIntOpErr {
    #[error("Operand must be a pointer type")]
    OperandTypeErr,
    #[error("Result must be a signless integer type")]
    ResultTypeErr,
}

/// Equivalent to LLVM's PtrToInt opcode.
/// ### Operands
/// | operand | description |
/// |-----|-------|
/// | `arg` | [PointerType] |
///
/// ### Result(s):
/// | result | description |
/// |-----|-------|
/// | `res` | Signless integer |
#[def_op("llvm.ptrtoint")]
#[format_op("$0 ` to ` type($0)")]
#[derive_op_interface_impl(OneResultInterface, OneOpdInterface, CastOpInterface)]
pub struct PtrToIntOp;

impl Verify for PtrToIntOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let loc = self.loc(ctx);
        // Ensure correctness of operand type.
        if !self.operand_type(ctx).deref(ctx).is::<PointerType>() {
            return verify_err!(loc, PtrToIntOpErr::OperandTypeErr);
        }
        // Ensure correctness of result type.
        if !self.result_type(ctx).deref(ctx).is::<IntegerType>() {
            return verify_err!(loc, PtrToIntOpErr::ResultTypeErr);
        }
        Ok(())
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
    /// Create a new [CondBrOp].
    pub fn new(
        ctx: &mut Context,
        condition: Value,
        true_dest: Ptr<BasicBlock>,
        true_dest_opds: Vec<Value>,
        false_dest: Ptr<BasicBlock>,
        false_dest_opds: Vec<Value>,
    ) -> Self {
        let (operands, segment_sizes) =
            Self::compute_segment_sizes(vec![vec![condition], true_dest_opds, false_dest_opds]);

        let op = CondBrOp {
            op: Operation::new(
                ctx,
                Self::get_opid_static(),
                vec![],
                operands,
                vec![true_dest, false_dest],
                0,
            ),
        };

        // Set the operand segment sizes attribute.
        op.set_operand_segment_sizes(ctx, segment_sizes);
        op
    }

    /// Get the condition value for the branch.
    pub fn condition(&self, ctx: &Context) -> Value {
        self.op.deref(ctx).get_operand(0)
    }
}

#[op_interface_impl]
impl OperandSegmentInterface for CondBrOp {}

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
                    combine::parser(move |parsable_state: &mut StateStream<'a>| {
                        let ctx = &mut parsable_state.state.ctx;
                        let op = CondBrOp::new(
                            ctx,
                            condition,
                            true_dest,
                            true_dest_opds.clone(),
                            false_dest,
                            false_dest_opds.clone(),
                        );

                        process_parsed_ssa_defs(parsable_state, &results, op.get_operation())?;
                        let op: OpObj = Box::new(op);
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

        // Skip the first segment, which is the condition.
        self.get_segment(ctx, succ_idx + 1)
    }
}

/// Equivalent to LLVM's Switch opcode.
///
/// ### Operands
/// | operand | description |
/// |-----|-------|
/// | `condition` | 1-bit signless integer |
/// | `default_dest_opds` | variadic of any type |
/// | `case_dest_opds` | variadic of any type |
///
/// ### Successors:
/// | Successor | description |
/// |-----|-------|
/// | `default_dest` | any successor |
/// | `case_dests` | any successor(s) |
#[def_op("llvm.switch")]
#[derive_attr_get_set(switch_case_values: CaseValuesAttr)]
pub struct SwitchOp;

#[derive(Clone)]
pub struct SwitchCase {
    pub value: IntegerAttr,
    pub dest: Ptr<BasicBlock>,
    pub dest_opds: Vec<Value>,
}

impl Printable for SwitchCase {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &pliron::printable::State,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        write!(
            f,
            "{{ {}: ^{}({}) }}",
            self.value.disp(ctx),
            self.dest.deref(ctx).unique_name(ctx),
            list_with_sep(
                &self.dest_opds,
                pliron::printable::ListSeparator::CharSpace(',')
            )
            .disp(ctx)
        )
    }
}

impl Parsable for SwitchCase {
    type Arg = ();
    type Parsed = Self;

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        let mut parser = between(
            token('{'),
            token('}'),
            (
                spaced(IntegerAttr::parser(())),
                spaced(token(':')),
                spaced(block_opd_parser()),
                delimited_list_parser('(', ')', ',', ssa_opd_parser()),
                spaces(),
            ),
        );

        let ((value, _colon, dest, dest_opds, _spaces), _) =
            parser.parse_stream(state_stream).into_result()?;

        Ok(SwitchCase {
            value,
            dest,
            dest_opds,
        })
        .into_parse_result()
    }
}

impl Printable for SwitchOp {
    fn fmt(
        &self,
        ctx: &Context,
        state: &pliron::printable::State,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        let op = self.get_operation().deref(ctx);
        let condition = op.get_operand(0);

        let default_successor = op
            .successors()
            .next()
            .expect("SwitchOp must have at least one successor");
        let num_total_successors = op.get_num_successors();

        write!(
            f,
            "{} {}, ^{}({})",
            op.get_opid(),
            condition.disp(ctx),
            default_successor.unique_name(ctx).disp(ctx),
            iter_with_sep(
                self.successor_operands(ctx, 0).iter(),
                pliron::printable::ListSeparator::CharSpace(',')
            )
            .disp(ctx),
        )?;

        if num_total_successors < 2 {
            writeln!(f, "[]")?;
            return Ok(());
        }

        let cases = self.cases(ctx);

        write!(f, "{}[", indented_nl(state))?;
        indented_block!(state, {
            write!(f, "{}", indented_nl(state))?;
            list_with_sep(&cases, pliron::printable::ListSeparator::CharNewline(','))
                .fmt(ctx, state, f)?;
        });
        write!(f, "{}]", indented_nl(state))?;

        Ok(())
    }
}

impl Parsable for SwitchOp {
    type Arg = Vec<(Identifier, Location)>;
    type Parsed = OpObj;

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        if !arg.is_empty() {
            input_err!(
                state_stream.loc(),
                op_interfaces::ZeroResultVerifyErr(Self::get_opid_static().to_string())
            )?
        }

        // Parse the condition operand.
        let condition = ssa_opd_parser().skip(spaced(token(',')));
        let default_successor = block_opd_parser();
        let default_operands = delimited_list_parser('(', ')', ',', ssa_opd_parser());
        let cases = delimited_list_parser('[', ']', ',', SwitchCase::parser(()));

        let final_parser = spaced(condition)
            .and(default_successor)
            .skip(spaces())
            .and(default_operands)
            .skip(spaces())
            .and(cases);

        final_parser
            .then(
                move |(((condition, default_dest), default_dest_opds), cases)| {
                    let results = arg.clone();
                    combine::parser(move |parsable_state: &mut StateStream<'a>| {
                        let ctx = &mut parsable_state.state.ctx;
                        let op = SwitchOp::new(
                            ctx,
                            condition,
                            default_dest,
                            default_dest_opds.clone(),
                            cases.clone(),
                        );

                        process_parsed_ssa_defs(parsable_state, &results, op.get_operation())?;
                        let op: OpObj = Box::new(op);
                        Ok(op).into_parse_result()
                    })
                },
            )
            .parse_stream(state_stream)
            .into()
    }
}

impl SwitchOp {
    /// Create a new [SwitchOp].
    pub fn new(
        ctx: &mut Context,
        condition: Value,
        default_dest: Ptr<BasicBlock>,
        default_dest_opds: Vec<Value>,
        cases: Vec<SwitchCase>,
    ) -> Self {
        let case_values: Vec<IntegerAttr> = cases.iter().map(|case| case.value.clone()).collect();

        let case_operands = cases
            .iter()
            .map(|case| case.dest_opds.clone())
            .collect::<Vec<_>>();

        let mut operand_segments = vec![vec![condition], default_dest_opds];
        operand_segments.extend(case_operands);
        let (operands, segment_sizes) = Self::compute_segment_sizes(operand_segments);

        let case_dests = cases.iter().map(|case| case.dest);
        let successors = vec![default_dest].into_iter().chain(case_dests).collect();
        let op = SwitchOp {
            op: Operation::new(
                ctx,
                Self::get_opid_static(),
                vec![],
                operands,
                successors,
                0,
            ),
        };

        // Set the operand segment sizes attribute.
        op.set_operand_segment_sizes(ctx, segment_sizes);
        // Set the case values
        op.set_attr_switch_case_values(ctx, CaseValuesAttr(case_values));
        op
    }

    /// Get the cases of this switch operation.
    /// (The default case cannot be / isn't included here).
    pub fn cases(&self, ctx: &Context) -> Vec<SwitchCase> {
        let case_values = &*self
            .get_attr_switch_case_values(ctx)
            .expect("SwitchOp missing or incorrect case values attribute");

        let op = self.get_operation().deref(ctx);
        // Skip the first one, which is the default successor.
        let successors = op.successors().skip(1);

        successors
            .zip(case_values.0.iter())
            .enumerate()
            .map(|(i, (dest, value))| {
                // i+1 here because the first successor is the default destination.
                let dest_opds = self.successor_operands(ctx, i + 1);
                SwitchCase {
                    value: value.clone(),
                    dest,
                    dest_opds,
                }
            })
            .collect()
    }

    /// Get the condition value for the switch.
    pub fn condition(&self, ctx: &Context) -> Value {
        self.get_operation().deref(ctx).get_operand(0)
    }

    /// Get the default destination of this switch operation.
    pub fn default_dest(&self, ctx: &Context) -> Ptr<BasicBlock> {
        self.get_operation().deref(ctx).get_successor(0)
    }
}

impl IsTerminatorInterface for SwitchOp {}
impl BranchOpInterface for SwitchOp {
    fn successor_operands(&self, ctx: &Context, succ_idx: usize) -> Vec<Value> {
        // Skip the first segment, which is the condition.
        self.get_segment(ctx, succ_idx + 1)
    }
}

impl OperandSegmentInterface for SwitchOp {}

#[derive(Error, Debug)]
pub enum SwitchOpVerifyErr {
    #[error("SwitchOp has no or incorrect case values attribute")]
    CaseValuesAttrErr,
    #[error("SwitchOp has no or incorrect default destination")]
    DefaultDestErr,
    #[error("SwitchOp has no condition operand or is not an integer")]
    ConditionErr,
}

impl Verify for SwitchOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let loc = self.loc(ctx);

        let Some(case_values) = self.get_attr_switch_case_values(ctx) else {
            verify_err!(loc.clone(), SwitchOpVerifyErr::CaseValuesAttrErr)?
        };

        let op = &*self.get_operation().deref(ctx);

        if op.get_num_successors() < 1 {
            verify_err!(loc.clone(), SwitchOpVerifyErr::DefaultDestErr)?;
        }

        if op.get_num_operands() < 1 {
            verify_err!(loc.clone(), SwitchOpVerifyErr::ConditionErr)?;
        }

        let condition_ty = pliron::r#type::Typed::get_type(&op.get_operand(0), ctx);
        let condition_ty = TypePtr::<IntegerType>::from_ptr(condition_ty, ctx)?;

        if let Some(case_value) = case_values.0.first() {
            // Ensure that the case value type matches the condition type.
            if case_value.get_type() != condition_ty {
                verify_err!(loc, SwitchOpVerifyErr::ConditionErr)?;
            }
        }

        Ok(())
    }
}

/// A way to express whether a GEP index is a constant or an SSA value
#[derive(Clone)]
pub enum GepIndex {
    Constant(u32),
    Value(Value),
}

impl Printable for GepIndex {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &pliron::printable::State,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        match self {
            GepIndex::Constant(c) => write!(f, "{c}"),
            GepIndex::Value(v) => write!(f, "{}", v.disp(ctx)),
        }
    }
}

#[derive(Error, Debug)]
pub enum GetElementPtrOpErr {
    #[error("GetElementPtrOp has no or incorrect indices attribute")]
    IndicesAttrErr,
    #[error("The indices on this GEP are invalid for its source element type")]
    IndicesErr,
}

// Equivalent to LLVM's GetElementPtr.
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
    "`<` attr($gep_src_elem_type, $TypeAttr) `>` ` (` operands(CharSpace(`,`)) `)` attr($gep_indices, $GepIndicesAttr) ` : ` type($0)"
)]
#[derive_op_interface_impl(OneResultInterface)]
#[derive_attr_get_set(gep_src_elem_type : TypeAttr, gep_indices : GepIndicesAttr)]
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
        let loc = self.loc(ctx);
        // Ensure that we have the indices as an attribute.
        if self.get_attr_gep_indices(ctx).is_none() {
            verify_err!(loc, GetElementPtrOpErr::IndicesAttrErr)?
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
        let op = GetElementPtrOp { op };

        op.set_attr_gep_indices(ctx, GepIndicesAttr(attr));
        op.set_attr_gep_src_elem_type(ctx, src_elem_type);
        Ok(op)
    }

    /// Get the source pointer's element type.
    pub fn src_elem_type(&self, ctx: &Context) -> Ptr<TypeObj> {
        self.get_attr_gep_src_elem_type(ctx)
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
        self.get_attr_gep_indices(ctx)
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
#[def_op("llvm.call")]
#[derive_op_interface_impl(OneResultInterface)]
#[derive_attr_get_set(call_callee : IdentifierAttr)]
pub struct CallOp;

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
                let op = CallOp { op };
                op.set_attr_call_callee(ctx, IdentifierAttr::new(cval));
                op
            }
            CallOpCallable::Indirect(csym) => {
                args.insert(0, csym);
                let op =
                    Operation::new(ctx, Self::get_opid_static(), vec![res_ty], args, vec![], 0);
                CallOp { op }
            }
        };
        op.set_callee_type(ctx, callee_ty);
        op
    }
}

#[derive(Error, Debug)]
pub enum SymbolUserOpVerifyErr {
    #[error("Symbol {0} not found")]
    SymbolNotFound(String),
    #[error("Function {0} should have been builtin.func")]
    NotBuiltinFunc(String),
    #[error("AddressOf Op can only refer to a function or a global variable")]
    AddressOfInvalidReference,
    #[error("Function call has incorrect type: {0}")]
    FuncTypeErr(String),
}

#[op_interface_impl]
impl SymbolUserOpInterface for CallOp {
    fn verify_symbol_uses(
        &self,
        ctx: &Context,
        symbol_tables: &mut SymbolTableCollection,
    ) -> Result<()> {
        match self.callee(ctx) {
            CallOpCallable::Direct(callee_sym) => {
                let Some(callee) = symbol_tables.lookup_symbol_in_nearest_table(
                    ctx,
                    self.get_operation(),
                    &callee_sym,
                ) else {
                    return verify_err!(
                        self.loc(ctx),
                        SymbolUserOpVerifyErr::SymbolNotFound(callee_sym.to_string())
                    );
                };
                let Some(func_op) = (&*callee as &dyn Op).downcast_ref::<FuncOp>() else {
                    return verify_err!(
                        self.loc(ctx),
                        SymbolUserOpVerifyErr::NotBuiltinFunc(callee_sym.to_string())
                    );
                };
                let func_op_ty = func_op.get_type(ctx).deref(ctx);
                let Some(func_op_ty) = func_op_ty.downcast_ref::<FunctionType>() else {
                    return verify_err!(
                        self.loc(ctx),
                        SymbolUserOpVerifyErr::FuncTypeErr("Calle is not a function".to_string())
                    );
                };

                let callee_ty = &*self.callee_type(ctx).deref(ctx);
                if func_op_ty != callee_ty {
                    return verify_err!(
                        self.loc(ctx),
                        SymbolUserOpVerifyErr::FuncTypeErr(format!(
                            "expected {}, got {}",
                            func_op_ty.disp(ctx),
                            callee_ty.disp(ctx)
                        ))
                    );
                }
            }
            CallOpCallable::Indirect(pointer) => {
                use pliron::r#type::Typed;
                if !pointer.get_type(ctx).deref(ctx).is::<PointerType>() {
                    return verify_err!(
                        self.loc(ctx),
                        SymbolUserOpVerifyErr::FuncTypeErr("Callee must be a pointer".to_string())
                    );
                }
            }
        }
        Ok(())
    }

    fn used_symbols(&self, ctx: &Context) -> Vec<Identifier> {
        match self.callee(ctx) {
            CallOpCallable::Direct(identifier) => vec![identifier],
            CallOpCallable::Indirect(_) => vec![],
        }
    }
}

#[op_interface_impl]
impl CallOpInterface for CallOp {
    fn callee(&self, ctx: &Context) -> CallOpCallable {
        let op = self.op.deref(ctx);
        if let Some(callee_sym) = self.get_attr_call_callee(ctx) {
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

impl Printable for CallOp {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &pliron::printable::State,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        let callee = self.callee(ctx);
        write!(
            f,
            "{} = {} ",
            self.get_result(ctx).disp(ctx),
            self.get_opid()
        )?;
        match callee {
            CallOpCallable::Direct(callee_sym) => {
                write!(f, "@{callee_sym}")?;
            }
            CallOpCallable::Indirect(callee_val) => {
                write!(f, "{}", callee_val.disp(ctx))?;
            }
        }
        let args = self.args(ctx);
        let ty = self.callee_type(ctx);
        write!(
            f,
            " ({}) : {}",
            list_with_sep(&args, pliron::printable::ListSeparator::CharSpace(',')).disp(ctx),
            ty.disp(ctx)
        )?;
        Ok(())
    }
}

impl Parsable for CallOp {
    type Arg = Vec<(Identifier, Location)>;
    type Parsed = OpObj;

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        results: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        let direct_callee = combine::token('@')
            .with(Identifier::parser(()))
            .map(CallOpCallable::Direct);
        let indirect_callee = ssa_opd_parser().map(CallOpCallable::Indirect);
        let callee_parser = direct_callee.or(indirect_callee);
        let args_parser = delimited_list_parser('(', ')', ',', ssa_opd_parser());
        let ty_parser = spaced(combine::token(':')).with(TypePtr::<FunctionType>::parser(()));

        let mut final_parser = spaced(callee_parser)
            .and(spaced(args_parser))
            .and(ty_parser)
            .then(move |((callee, args), ty)| {
                let results = results.clone();
                combine::parser(move |parsable_state: &mut StateStream<'a>| {
                    let ctx = &mut parsable_state.state.ctx;
                    let op = CallOp::new(ctx, callee.clone(), ty, args.clone());
                    process_parsed_ssa_defs(parsable_state, &results, op.get_operation())?;
                    Ok(Box::new(op) as Box<dyn Op>).into_parse_result()
                })
            });

        final_parser.parse_stream(state_stream).into_result()
    }
}

impl Verify for CallOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        // Check that the argument and result types match the callee type.
        let callee_ty = &*self.callee_type(ctx).deref(ctx);
        // Check the function type against the arguments.
        let args = self.args(ctx);
        let expected_args = callee_ty.get_inputs();
        if args.len() != expected_args.len() {
            return verify_err!(
                self.loc(ctx),
                SymbolUserOpVerifyErr::FuncTypeErr("arguement count mismatch.".to_string())
            );
        }
        use pliron::r#type::Typed;
        for (arg_idx, (arg, expected_arg)) in args.iter().zip(expected_args.iter()).enumerate() {
            if arg.get_type(ctx) != *expected_arg {
                return verify_err!(
                    self.loc(ctx),
                    SymbolUserOpVerifyErr::FuncTypeErr(format!(
                        "arguement {} type mismatch: expected {}, got {}",
                        arg_idx,
                        expected_arg.disp(ctx),
                        arg.get_type(ctx).disp(ctx)
                    ))
                );
            }
        }

        if callee_ty.get_results().len() > 1 {
            return verify_err!(
                self.loc(ctx),
                SymbolUserOpVerifyErr::FuncTypeErr(
                    "LLVM dialect allows only a single result".to_string()
                )
            );
        }

        if let Some(res_ty) = callee_ty.get_results().first()
            && self.result_type(ctx) != *res_ty
        {
            return verify_err!(
                self.loc(ctx),
                SymbolUserOpVerifyErr::FuncTypeErr(format!(
                    "result type mismatch: expected {}, got {}",
                    res_ty.disp(ctx),
                    self.result_type(ctx).disp(ctx)
                ))
            );
        }

        Ok(())
    }
}

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
#[format_op("`: ` type($0)")]
pub struct UndefOp;
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

/// Numeric (integer or floating point) constant.
/// See MLIR's [llvm.mlir.constant](https://mlir.llvm.org/docs/Dialects/LLVM/#llvmmlirconstant-llvmconstantop).
///
/// Results:
///
/// | result | description |
/// |-----|-------|
/// | `result` | any type |
#[def_op("llvm.constant")]
#[derive_op_interface_impl(ZeroOpdInterface, OneResultInterface)]
#[format_op("`<` $constant_value `>` ` : ` type($0)")]
#[derive_attr_get_set(constant_value)]
pub struct ConstantOp;

impl ConstantOp {
    /// Get the constant value that this Op defines.
    pub fn get_value(&self, ctx: &Context) -> AttrObj {
        self.get_attr_constant_value(ctx).unwrap().clone()
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
        let op = ConstantOp { op };
        op.set_attr_constant_value(ctx, value);
        op
    }
}

#[derive(Error, Debug)]
#[error("{}: Unexpected type", ConstantOp::get_opid_static())]
pub enum ConstantOpVerifyErr {
    #[error("ConstantOp must have either an integer or a float value")]
    InvalidValue,
}

impl Verify for ConstantOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let loc = self.loc(ctx);
        let value = self.get_value(ctx);
        if !(value.is::<IntegerAttr>()/* || value.is::<FloatAttr>() */) {
            return verify_err!(loc, ConstantOpVerifyErr::InvalidValue)?;
        }
        Ok(())
    }
}

/// Same as MLIR's LLVM dialect [ZeroOp](https://mlir.llvm.org/docs/Dialects/LLVM/#llvmmlirzero-llvmzeroop)
/// It creates a zero-initialized value of the specified LLVM IR dialect type.
/// Results:
///
/// | result | description |
/// |-----|-------|
/// | `result` | any type |
#[def_op("llvm.zero")]
#[derive_op_interface_impl(ZeroOpdInterface, OneResultInterface)]
#[format_op("`: ` type($0)")]
pub struct ZeroOp;
impl_verify_succ!(ZeroOp);

impl ZeroOp {
    /// Create a new [ZeroOp].
    pub fn new(ctx: &mut Context, result_ty: Ptr<TypeObj>) -> Self {
        let op = Operation::new(
            ctx,
            Self::get_opid_static(),
            vec![result_ty],
            vec![],
            vec![],
            0,
        );
        ZeroOp { op }
    }
}

#[derive(Error, Debug)]
pub enum GlobalOpVerifyErr {
    #[error("GlobalOp must have a type")]
    MissingType,
}

/// Same as MLIR's LLVM dialect [GlobalOp](https://mlir.llvm.org/docs/Dialects/LLVM/#llvmmlirglobal-llvmglobalop)
/// It creates a global variable of the specified LLVM IR dialect type.
/// An initializer can be specified either as an attribute or in the
/// operation's initializer region, ending with a return.
#[def_op("llvm.global")]
#[derive_op_interface_impl(
    IsolatedFromAboveInterface,
    ZeroOpdInterface,
    ZeroResultInterface,
    SymbolOpInterface,
    SingleBlockRegionInterface
)]
#[derive_attr_get_set(global_type : TypeAttr, global_initializer)]
pub struct GlobalOp;

impl GlobalOp {
    /// Create a new [GlobalOp]. An initializer region can be added later if needed.
    pub fn new(ctx: &mut Context, name: Identifier, ty: Ptr<TypeObj>) -> Self {
        let op = Operation::new(ctx, Self::get_opid_static(), vec![], vec![], vec![], 0);
        let op = GlobalOp { op };
        op.set_symbol_name(ctx, name);
        op.set_attr_global_type(ctx, TypeAttr::new(ty));
        op
    }
}

impl pliron::r#type::Typed for GlobalOp {
    fn get_type(&self, ctx: &Context) -> Ptr<TypeObj> {
        pliron::r#type::Typed::get_type(
            &*self
                .get_attr_global_type(ctx)
                .expect("GlobalOp missing or has incorrect type attribute"),
            ctx,
        )
    }
}

impl GlobalOp {
    /// Get the initializer value of this global variable.
    pub fn get_initializer_value(&self, ctx: &Context) -> Option<AttrObj> {
        self.get_attr_global_initializer(ctx).map(|v| v.clone())
    }

    /// Get the initializer region's block of this global variable.
    /// This is a block that ends with a return operation.
    /// The return operation must have the same type as the global variable.
    pub fn get_initializer_block(&self, ctx: &Context) -> Option<Ptr<BasicBlock>> {
        (self.op.deref(ctx).num_regions() > 0).then(|| self.get_body(ctx, 0))
    }

    /// Get the initializer region of this global variable.
    pub fn get_initializer_region(&self, ctx: &Context) -> Option<Ptr<Region>> {
        (self.op.deref(ctx).num_regions() > 0)
            .then(|| self.get_operation().deref(ctx).get_region(0))
    }

    /// Set a simple initializer value for this global variable.
    pub fn set_initializer_value(&self, ctx: &Context, value: AttrObj) {
        self.set_attr_global_initializer(ctx, value);
    }

    /// Add an initializer region (with an entry block) for this global variable.
    /// There shouldn't already be one.
    pub fn add_initializer_region(&self, ctx: &mut Context) -> Ptr<Region> {
        assert!(
            self.get_initializer_value(ctx).is_none(),
            "Attempt to create an initializer region when there already is an initializer value"
        );
        let region = Operation::add_region(self.get_operation(), ctx);
        let entry = BasicBlock::new(ctx, Some("entry".try_into().unwrap()), vec![]);
        entry.insert_at_front(region, ctx);

        region
    }
}

impl Verify for GlobalOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let loc = self.loc(ctx);

        // The name must be set. That is checked by the SymbolOpInterface.
        // So we check that other attributes are set. Start with type.
        if self.get_attr_global_type(ctx).is_none() {
            return verify_err!(loc, GlobalOpVerifyErr::MissingType);
        }

        // Check that there is at most one initializer
        if self.get_initializer_value(ctx).is_some() && self.get_initializer_region(ctx).is_some() {
            return verify_err!(loc, GlobalOpVerifyErr::MissingType);
        }

        Ok(())
    }
}

impl Printable for GlobalOp {
    fn fmt(
        &self,
        ctx: &Context,
        state: &pliron::printable::State,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        write!(
            f,
            "{} @{} : {}",
            self.get_opid(),
            self.get_symbol_name(ctx),
            <Self as pliron::r#type::Typed>::get_type(self, ctx).disp(ctx)
        )?;

        if let Some(init_value) = self.get_initializer_value(ctx) {
            write!(f, " = {}", init_value.disp(ctx))?;
        }

        if let Some(init_region) = self.get_initializer_region(ctx) {
            write!(f, " = {}", init_region.print(ctx, state))?;
        }

        Ok(())
    }
}

impl Parsable for GlobalOp {
    type Arg = Vec<(Identifier, Location)>;
    type Parsed = OpObj;
    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        results: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        let loc = state_stream.loc();
        if !results.is_empty() {
            return input_err!(loc, "GlobalOp must cannot have results")?;
        }
        let name_parser = combine::token('@').with(Identifier::parser(()));
        let type_parser = type_parser();

        let mut parser = name_parser
            .skip(spaced(combine::token(':')))
            .and(type_parser);

        let ((name, ty), _) = parser.parse_stream(state_stream).into_result()?;
        let op = GlobalOp::new(state_stream.state.ctx, name, ty);

        enum Initializer {
            Value(AttrObj),
            Region(Ptr<Region>),
        }
        // Parse optional initializer value or region.
        let initializer_parser = combine::token('=').skip(spaces()).with(
            attr_parser()
                .map(Initializer::Value)
                .or(Region::parser(op.get_operation()).map(Initializer::Region)),
        );

        let initializer = spaces()
            .with(combine::optional(initializer_parser))
            .parse_stream(state_stream)
            .into_result()?;

        if let Some(initializer) = initializer.0 {
            match initializer {
                Initializer::Value(v) => op.set_initializer_value(state_stream.state.ctx, v),
                Initializer::Region(_r) => {
                    // Nothing to do since the region is already added to the operation during parsing.
                }
            }
        }

        Ok(Box::new(op) as OpObj).into_parse_result()
    }
}

/// Same as MLIR's LLVM dialect [AddressOfOp](https://mlir.llvm.org/docs/Dialects/LLVM/#llvmmliraddressof-llvmaddressofop).
/// Creates an SSA value containing a pointer to a global value (function, variable etc).
///
/// ### Results:
///
/// | result | description |
/// |-----|-------|
/// | `result` | LLVM pointer type |
///
#[def_op("llvm.addressof")]
#[derive_op_interface_impl(OneResultInterface)]
#[format_op("`@` attr($global_name, $IdentifierAttr) ` : ` type($0)")]
#[derive_attr_get_set(global_name : IdentifierAttr)]
pub struct AddressOfOp;

impl_verify_succ!(AddressOfOp);

impl AddressOfOp {
    /// Create a new [AddressOfOp].
    pub fn new(ctx: &mut Context, global_name: Identifier) -> Self {
        let result_type = PointerType::get(ctx).into();
        let op = Operation::new(
            ctx,
            Self::get_opid_static(),
            vec![result_type],
            vec![],
            vec![],
            0,
        );
        let op = AddressOfOp { op };
        op.set_attr_global_name(ctx, IdentifierAttr::new(global_name));
        op
    }

    /// Get the global name that this refers to.
    pub fn get_global_name(&self, ctx: &Context) -> Identifier {
        self.get_attr_global_name(ctx)
            .expect("AddressOfOp missing or has incorrect global_name attribute type")
            .clone()
            .into()
    }

    /// If this operation referes to a global, get it.
    pub fn get_global(
        &self,
        ctx: &Context,
        symbol_tables: &mut SymbolTableCollection,
    ) -> Option<GlobalOp> {
        let global_name = self.get_global_name(ctx);
        symbol_tables
            .lookup_symbol_in_nearest_table(ctx, self.get_operation(), &global_name)
            .and_then(|sym_op| {
                (sym_op as Box<dyn Op>)
                    .downcast::<GlobalOp>()
                    .map(|op| *op)
                    .ok()
            })
    }

    /// If this operation refers to a function, get it.
    pub fn get_function(
        &self,
        ctx: &Context,
        symbol_tables: &mut SymbolTableCollection,
    ) -> Option<FuncOp> {
        let global_name = self.get_global_name(ctx);
        symbol_tables
            .lookup_symbol_in_nearest_table(ctx, self.get_operation(), &global_name)
            .and_then(|sym_op| {
                (sym_op as Box<dyn Op>)
                    .downcast::<FuncOp>()
                    .map(|op| *op)
                    .ok()
            })
    }
}

impl SymbolUserOpInterface for AddressOfOp {
    fn used_symbols(&self, ctx: &Context) -> Vec<Identifier> {
        vec![self.get_global_name(ctx)]
    }

    fn verify_symbol_uses(
        &self,
        ctx: &Context,
        symbol_tables: &mut SymbolTableCollection,
    ) -> Result<()> {
        let loc = self.loc(ctx);
        let global_name = self.get_global_name(ctx);
        let Some(symbol) =
            symbol_tables.lookup_symbol_in_nearest_table(ctx, self.get_operation(), &global_name)
        else {
            return verify_err!(
                loc,
                SymbolUserOpVerifyErr::SymbolNotFound(global_name.to_string())
            );
        };

        // Symbol can only be a FuncOp or a GlobalOp
        let is_global = (&*symbol as &dyn Op).is::<GlobalOp>();
        let is_func = (&*symbol as &dyn Op).is::<FuncOp>();
        if !is_global && !is_func {
            return verify_err!(loc, SymbolUserOpVerifyErr::AddressOfInvalidReference);
        }

        Ok(())
    }
}

#[derive(Error, Debug)]
enum IntCastVerifyErr {
    #[error("Result must be an integer")]
    ResultTypeErr,
    #[error("Operand must be an integer")]
    OperandTypeErr,
    #[error("Result type must be larger than operand type")]
    ResultTypeSmallerThanOperand,
    #[error("Result type must be smaller than operand type")]
    ResultTypeLargerThanOperand,
    #[error("Result type must be equal to operand type")]
    ResultTypeEqualToOperand,
}

/// Ensure that the integer cast operation is valid.
/// This checks that the result type is an integer and that the operand type is also an integer.
/// It also checks that the result type is larger or smaller than the operand type (`cmp` operand).
fn integer_cast_verify(op: &Operation, ctx: &Context, cmp: ICmpPredicateAttr) -> Result<()> {
    use pliron::r#type::Typed;

    let loc = op.loc();
    let res_ty = op.get_type(0).deref(ctx);
    let opd_ty = op.get_operand(0).get_type(ctx).deref(ctx);
    let Some(res_ty) = res_ty.downcast_ref::<IntegerType>() else {
        return verify_err!(loc, IntCastVerifyErr::ResultTypeErr);
    };
    let Some(opd_ty) = opd_ty.downcast_ref::<IntegerType>() else {
        return verify_err!(loc, IntCastVerifyErr::OperandTypeErr);
    };

    match cmp {
        ICmpPredicateAttr::SLT | ICmpPredicateAttr::ULT => {
            if res_ty.get_width() >= opd_ty.get_width() {
                return verify_err!(loc, IntCastVerifyErr::ResultTypeLargerThanOperand);
            }
        }
        ICmpPredicateAttr::SGT | ICmpPredicateAttr::UGT => {
            if res_ty.get_width() <= opd_ty.get_width() {
                return verify_err!(loc, IntCastVerifyErr::ResultTypeSmallerThanOperand);
            }
        }
        ICmpPredicateAttr::SLE | ICmpPredicateAttr::ULE => {
            if res_ty.get_width() > opd_ty.get_width() {
                return verify_err!(loc, IntCastVerifyErr::ResultTypeLargerThanOperand);
            }
        }
        ICmpPredicateAttr::SGE | ICmpPredicateAttr::UGE => {
            if res_ty.get_width() < opd_ty.get_width() {
                return verify_err!(loc, IntCastVerifyErr::ResultTypeSmallerThanOperand);
            }
        }
        ICmpPredicateAttr::EQ | ICmpPredicateAttr::NE => {
            if res_ty.get_width() != opd_ty.get_width() {
                return verify_err!(loc, IntCastVerifyErr::ResultTypeEqualToOperand);
            }
        }
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
        integer_cast_verify(
            &self.get_operation().deref(ctx),
            ctx,
            ICmpPredicateAttr::SGT,
        )
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
        integer_cast_verify(
            &self.get_operation().deref(ctx),
            ctx,
            ICmpPredicateAttr::UGT,
        )
    }
}

/// Equivalent to LLVM's trunc opcode.
/// ### Operands
/// | operand | description |
/// |-----|-------|
/// | `arg` | Signless integer |
/// ### Result(s):
/// | result | description |
/// |-----|-------|
/// | `res` | Signless integer |
#[def_op("llvm.trunc")]
#[derive_op_interface_impl(CastOpInterface, OneResultInterface, OneOpdInterface)]
#[format_op("$0 ` to ` type($0)")]
pub struct TruncOp;

impl Verify for TruncOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        integer_cast_verify(
            &self.get_operation().deref(ctx),
            ctx,
            ICmpPredicateAttr::ULT,
        )
    }
}

/// Equivalent to LLVM's InsertValue opcode.
///
/// ### Operands
/// | operand | description |
/// |-----|-------|
/// | `aggregate` | LLVM aggregate type |
/// | `value` | LLVM type |
///
/// ### Result(s):
/// | result | description |
/// |-----|-------|
/// | `res` | LLVM aggregate type |
#[def_op("llvm.insert_value")]
#[format_op(
    "$0 attr($insert_value_indices, $InsertExtractValueIndicesAttr) `, ` $1 ` : ` type($0)"
)]
#[derive_attr_get_set(insert_value_indices : InsertExtractValueIndicesAttr)]
#[derive_op_interface_impl(OneResultInterface)]
pub struct InsertValueOp;

impl InsertValueOp {
    /// Create a new [InsertValueOp].
    /// `aggregate` is the aggregate type and `value` is the value to insert.
    /// `indices` is the list of indices to insert the value at.
    /// The `indices` must be valid for the given `aggregate` type.
    pub fn new(ctx: &mut Context, aggregate: Value, value: Value, indices: Vec<u32>) -> Self {
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
        let op = InsertValueOp { op };
        op.set_attr_insert_value_indices(ctx, InsertExtractValueIndicesAttr(indices));
        op
    }

    /// Get the indices for inserting value into aggregate.
    pub fn indices(&self, ctx: &Context) -> Vec<u32> {
        self.get_attr_insert_value_indices(ctx).unwrap().clone().0
    }
}

impl Verify for InsertValueOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let loc = self.loc(ctx);
        // Ensure that we have the indices as an attribute.
        if self.get_attr_insert_value_indices(ctx).is_none() {
            verify_err!(loc.clone(), InsertExtractValueErr::IndicesAttrErr)?
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
                    return verify_err!(loc, InsertExtractValueErr::ValueTypeErr);
                }
            }
        }

        Ok(())
    }
}

/// Equivalent to LLVM's ExtractValue opcode.
///
/// ### Operands
/// | operand | description |
/// |-----|-------|
/// | `aggregate` | LLVM aggregate type |
///
/// ### Result(s):
/// | result | description |
/// |-----|-------|
/// | `res` | LLVM type |
#[def_op("llvm.extract_value")]
#[format_op("$0 attr($extract_value_indices, $InsertExtractValueIndicesAttr) ` : ` type($0)")]
#[derive_op_interface_impl(OneResultInterface, OneOpdInterface)]
#[derive_attr_get_set(extract_value_indices : InsertExtractValueIndicesAttr)]
pub struct ExtractValueOp;

impl Verify for ExtractValueOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let loc = self.loc(ctx);
        // Ensure that we have the indices as an attribute.
        if self.get_attr_extract_value_indices(ctx).is_none() {
            verify_err!(loc.clone(), InsertExtractValueErr::IndicesAttrErr)?
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
                    return verify_err!(loc, InsertExtractValueErr::ValueTypeErr);
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
        let op = ExtractValueOp { op };
        op.set_attr_extract_value_indices(ctx, InsertExtractValueIndicesAttr(indices));
        Ok(op)
    }

    /// Get the indices for extracting value from aggregate.
    pub fn indices(&self, ctx: &Context) -> Vec<u32> {
        self.get_attr_extract_value_indices(ctx).unwrap().clone().0
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
                    return arg_err_noloc!(InsertExtractValueErr::InvalidIndicesErr);
                }
                indexed_type_inner(ctx, st.field_type(idx as usize), idx_itr)
            } else if let Some(at) = aggr_type.downcast_ref::<ArrayType>() {
                if idx as u64 >= at.size() {
                    return arg_err_noloc!(InsertExtractValueErr::InvalidIndicesErr);
                }
                indexed_type_inner(ctx, at.elem_type(), idx_itr)
            } else {
                arg_err_noloc!(InsertExtractValueErr::InvalidIndicesErr)
            }
        }
        indexed_type_inner(ctx, aggr_type, indices.iter().cloned())
    }
}

#[derive(Error, Debug)]
pub enum InsertExtractValueErr {
    #[error("Insert/Extract value instruction has no or incorrect indices attribute")]
    IndicesAttrErr,
    #[error("Invalid indices on insert/extract value instruction")]
    InvalidIndicesErr,
    #[error("Value being inserted / extracted does not match the type of the indexed aggregate")]
    ValueTypeErr,
}

/// Equivalent to LLVM's Select opcode.
///
/// ### Operands
/// | operand | description |
/// |-----|-------|
/// | `condition` | i1 |
/// | `true_dest` | any type |
/// | `false_dest` | any type |
///
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
    PtrToIntOp::register(ctx, PtrToIntOp::parser_fn);
    IntToPtrOp::register(ctx, IntToPtrOp::parser_fn);
    BrOp::register(ctx, BrOp::parser_fn);
    SwitchOp::register(ctx, SwitchOp::parser_fn);
    CondBrOp::register(ctx, CondBrOp::parser_fn);
    GetElementPtrOp::register(ctx, GetElementPtrOp::parser_fn);
    LoadOp::register(ctx, LoadOp::parser_fn);
    StoreOp::register(ctx, StoreOp::parser_fn);
    CallOp::register(ctx, CallOp::parser_fn);
    AddressOfOp::register(ctx, AddressOfOp::parser_fn);
    GlobalOp::register(ctx, GlobalOp::parser_fn);
    ConstantOp::register(ctx, ConstantOp::parser_fn);
    ZeroOp::register(ctx, ZeroOp::parser_fn);
    SExtOp::register(ctx, SExtOp::parser_fn);
    ZExtOp::register(ctx, ZExtOp::parser_fn);
    TruncOp::register(ctx, TruncOp::parser_fn);
    InsertValueOp::register(ctx, InsertValueOp::parser_fn);
    ExtractValueOp::register(ctx, ExtractValueOp::parser_fn);
    SelectOp::register(ctx, SelectOp::parser_fn);
    UndefOp::register(ctx, UndefOp::parser_fn);
    ReturnOp::register(ctx, ReturnOp::parser_fn);
}
