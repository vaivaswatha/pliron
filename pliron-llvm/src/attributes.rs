//! Attributes belonging to the LLVM dialect.

use combine::{between, choice, parser::char::string, token, Parser};
use pliron_derive::def_attribute;

use pliron::{
    context::Context,
    impl_verify_succ,
    irfmt::{
        parsers::{delimited_list_parser, int_parser},
        printers::list_with_sep,
    },
    parsable::{self, Parsable},
    printable::{Printable, State},
};

/// Integer overflow flags for arithmetic operations.
/// The description below is from LLVM's
/// [release notes](https://releases.llvm.org/2.6/docs/ReleaseNotes.html)
/// that added the flags.
/// "nsw" and "nuw" bits indicate that the operation is guaranteed to not overflow
/// (in the signed or unsigned case, respectively). This gives the optimizer more information
///  and can be used for things like C signed integer values, which are undefined on overflow.
#[def_attribute("llvm.integer_overlflow_flags")]
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum IntegerOverflowFlagsAttr {
    None,
    Nsw,
    Nuw,
}

impl Parsable for IntegerOverflowFlagsAttr {
    type Arg = ();
    type Parsed = Self;

    fn parse<'a>(
        state_stream: &mut parsable::StateStream<'a>,
        _arg: Self::Arg,
    ) -> parsable::ParseResult<'a, Self> {
        choice((
            string("none").map(|_| IntegerOverflowFlagsAttr::None),
            string("nsw").map(|_| IntegerOverflowFlagsAttr::Nsw),
            string("nuw").map(|_| IntegerOverflowFlagsAttr::Nuw),
        ))
        .parse_stream(state_stream)
        .into()
    }
}

impl_verify_succ!(IntegerOverflowFlagsAttr);

impl Printable for IntegerOverflowFlagsAttr {
    fn fmt(
        &self,
        _ctx: &Context,
        _state: &State,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        match self {
            IntegerOverflowFlagsAttr::None => write!(f, "none"),
            IntegerOverflowFlagsAttr::Nsw => write!(f, "nsw"),
            IntegerOverflowFlagsAttr::Nuw => write!(f, "nuw"),
        }
    }
}

#[def_attribute("llvm.icmp_predicate")]
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum ICmpPredicateAttr {
    EQ,
    NE,
    SLT,
    SLE,
    SGT,
    SGE,
    ULT,
    ULE,
    UGT,
    UGE,
}

impl Printable for ICmpPredicateAttr {
    fn fmt(
        &self,
        _ctx: &Context,
        _state: &State,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        match self {
            ICmpPredicateAttr::EQ => write!(f, "eq"),
            ICmpPredicateAttr::NE => write!(f, "ne"),
            ICmpPredicateAttr::SLT => write!(f, "slt"),
            ICmpPredicateAttr::SLE => write!(f, "sle"),
            ICmpPredicateAttr::SGT => write!(f, "sgt"),
            ICmpPredicateAttr::SGE => write!(f, "sge"),
            ICmpPredicateAttr::ULT => write!(f, "ult"),
            ICmpPredicateAttr::ULE => write!(f, "ule"),
            ICmpPredicateAttr::UGT => write!(f, "ugt"),
            ICmpPredicateAttr::UGE => write!(f, "uge"),
        }
    }
}

impl Parsable for ICmpPredicateAttr {
    type Arg = ();
    type Parsed = Self;

    fn parse<'a>(
        state_stream: &mut parsable::StateStream<'a>,
        _arg: Self::Arg,
    ) -> parsable::ParseResult<'a, Self> {
        choice((
            string("eq").map(|_| ICmpPredicateAttr::EQ),
            string("ne").map(|_| ICmpPredicateAttr::NE),
            string("slt").map(|_| ICmpPredicateAttr::SLT),
            string("sle").map(|_| ICmpPredicateAttr::SLE),
            string("sgt").map(|_| ICmpPredicateAttr::SGT),
            string("sge").map(|_| ICmpPredicateAttr::SGE),
            string("ult").map(|_| ICmpPredicateAttr::ULT),
            string("ule").map(|_| ICmpPredicateAttr::ULE),
            string("ugt").map(|_| ICmpPredicateAttr::UGT),
            string("uge").map(|_| ICmpPredicateAttr::UGE),
        ))
        .parse_stream(state_stream)
        .into()
    }
}
impl_verify_succ!(ICmpPredicateAttr);

/// An index for a GEP can be either a constant or an SSA operand.
/// Contrary to its name, this isn't an [Attribute][pliron::attribute::Attribute].
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum GepIndexAttr {
    /// This GEP index is a raw u32 compile time constant
    Constant(u32),
    /// This GEP Index is the SSA value in the containing
    /// [Operation](pliron::operation::Operation)s `operands[idx]`
    OperandIdx(usize),
}

impl Printable for GepIndexAttr {
    fn fmt(
        &self,
        _ctx: &Context,
        _state: &State,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        match self {
            GepIndexAttr::Constant(c) => write!(f, "c({c})"),
            GepIndexAttr::OperandIdx(i) => write!(f, "opd({i})"),
        }
    }
}

impl Parsable for GepIndexAttr {
    type Arg = ();
    type Parsed = Self;

    fn parse<'a>(
        state_stream: &mut parsable::StateStream<'a>,
        _arg: Self::Arg,
    ) -> parsable::ParseResult<'a, Self> {
        choice((string("c"), string("opd")))
            .and(between(token('('), token(')'), int_parser::<usize>()))
            .parse_stream(state_stream)
            .map(|(gidxt, i)| {
                if gidxt == "c" {
                    GepIndexAttr::Constant(i.try_into().unwrap())
                } else {
                    GepIndexAttr::OperandIdx(i)
                }
            })
            .into()
    }
}

#[def_attribute("llvm.gep_indices")]
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct GepIndicesAttr(pub Vec<GepIndexAttr>);

impl_verify_succ!(GepIndicesAttr);
impl Printable for GepIndicesAttr {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &State,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        write!(
            f,
            "[{}]",
            list_with_sep(&self.0, pliron::printable::ListSeparator::CharSpace(',')).disp(ctx)
        )
    }
}

impl Parsable for GepIndicesAttr {
    type Arg = ();
    type Parsed = Self;

    fn parse<'a>(
        state_stream: &mut parsable::StateStream<'a>,
        _arg: Self::Arg,
    ) -> parsable::ParseResult<'a, Self::Parsed> {
        delimited_list_parser('[', ']', ',', GepIndexAttr::parser(()))
            .parse_stream(state_stream)
            .map(GepIndicesAttr)
            .into()
    }
}
