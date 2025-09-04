//! Attributes belonging to the LLVM dialect.

use std::fmt::Display;

use combine::parser::char::spaces;
use combine::{Parser, choice};
use thiserror::Error;

use pliron::attribute::Attribute;
use pliron::builtin::attributes::IntegerAttr;
use pliron::common_traits::Verify;
use pliron::context::Context;
use pliron::derive::{def_attribute, format, format_attribute};
use pliron::location::Located;
use pliron::parsable::{IntoParseResult, Parsable};
use pliron::printable::Printable;
use pliron::result::Result;
use pliron::{
    impl_printable_for_display, impl_verify_succ, input_err, input_error, verify_err_noloc,
};

use crate::llvm_sys::core::FastmathFlags;

/// Integer overflow flags for arithmetic operations.
/// The description below is from LLVM's
/// [release notes](https://releases.llvm.org/2.6/docs/ReleaseNotes.html)
/// that added the flags.
/// "nsw" and "nuw" bits indicate that the operation is guaranteed to not overflow
/// (in the signed or unsigned case, respectively). This gives the optimizer more information
///  and can be used for things like C signed integer values, which are undefined on overflow.
#[def_attribute("llvm.integer_overlflow_flags")]
#[format_attribute]
#[derive(PartialEq, Eq, Clone, Debug, Default, Hash)]
pub struct IntegerOverflowFlagsAttr {
    pub nsw: bool,
    pub nuw: bool,
}

impl_verify_succ!(IntegerOverflowFlagsAttr);

#[def_attribute("llvm.fast_math_flags")]
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct FastmathFlagsAttr(pub FastmathFlags);

impl From<FastmathFlags> for FastmathFlagsAttr {
    fn from(value: FastmathFlags) -> Self {
        FastmathFlagsAttr(value)
    }
}

impl From<FastmathFlagsAttr> for FastmathFlags {
    fn from(attr: FastmathFlagsAttr) -> Self {
        attr.0
    }
}

impl_verify_succ!(FastmathFlagsAttr);

impl Display for FastmathFlagsAttr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<")?;
        bitflags::parser::to_writer(&self.0, &mut *f)?;
        write!(f, ">")
    }
}

impl_printable_for_display!(FastmathFlagsAttr);

#[derive(Debug, Error)]
#[error("Error parsing fastmath flags: {0}")]
pub struct FastmathFlagParseErr(pub bitflags::parser::ParseError);

impl Parsable for FastmathFlagsAttr {
    type Arg = ();

    type Parsed = Self;

    fn parse<'a>(
        state_stream: &mut pliron::parsable::StateStream<'a>,
        _arg: Self::Arg,
    ) -> pliron::parsable::ParseResult<'a, Self::Parsed> {
        let pos = state_stream.loc();
        let allowed_chars = combine::choice!(
            combine::parser::char::space().map(|c| c.to_string()),
            combine::parser::char::alpha_num().map(|c| c.to_string()),
            combine::parser::char::char('|').map(|c: char| c.to_string())
        );

        let (parsed, _): (Vec<String>, _) = combine::between(
            combine::parser::char::char('<').with(spaces()),
            spaces().with(combine::parser::char::char('>')),
            combine::many(allowed_chars),
        )
        .parse_stream(state_stream)
        .into_result()?;
        let parsed_string = parsed.concat();

        let (fast_math_flags, _) = bitflags::parser::from_str::<FastmathFlags>(&parsed_string)
            .map_err(|e| input_error!(pos.clone(), FastmathFlagParseErr(e)))
            .into_parse_result()?;

        Ok(FastmathFlagsAttr(fast_math_flags)).into_parse_result()
    }
}

#[def_attribute("llvm.icmp_predicate")]
#[format_attribute]
#[derive(PartialEq, Eq, Clone, Debug, Hash)]
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

impl_verify_succ!(ICmpPredicateAttr);

#[def_attribute("llvm.fcmp_predicate")]
#[format_attribute]
#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub enum FCmpPredicateAttr {
    False,
    OEQ,
    OGT,
    OGE,
    OLT,
    OLE,
    ONE,
    ORD,
    UEQ,
    UGT,
    UGE,
    ULT,
    ULE,
    UNE,
    UNO,
    True,
}
impl_verify_succ!(FCmpPredicateAttr);

/// An index for a GEP can be either a constant or an SSA operand.
/// Contrary to its name, this isn't an [Attribute][pliron::attribute::Attribute].
#[derive(PartialEq, Eq, Clone, Debug, Hash)]
#[format]
pub enum GepIndexAttr {
    /// This GEP index is a raw u32 compile time constant
    Constant(u32),
    /// This GEP Index is the SSA value in the containing
    /// [Operation](pliron::operation::Operation)s `operands[idx]`
    OperandIdx(usize),
}

#[def_attribute("llvm.gep_indices")]
#[format_attribute("`[` vec($0, CharSpace(`,`)) `]`")]
#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct GepIndicesAttr(pub Vec<GepIndexAttr>);
impl_verify_succ!(GepIndicesAttr);

/// An attribute that contains a list of case values for a switch operation.
#[def_attribute("llvm.case_values")]
#[derive(PartialEq, Eq, Clone, Debug, Hash)]
#[format_attribute("`[` vec($0, CharSpace(`,`)) `]`")]
pub struct CaseValuesAttr(pub Vec<IntegerAttr>);

#[derive(Debug, Error)]
#[error("Case values must be of the same type, but found different types: {0} and {1}")]
pub struct CaseValuesAttrVerifyErr(pub String, pub String);

impl Verify for CaseValuesAttr {
    fn verify(&self, ctx: &Context) -> Result<()> {
        self.0.windows(2).try_for_each(|pair| {
            pair[0].verify(ctx)?;
            if pair[0].get_type() != pair[1].get_type() {
                verify_err_noloc!(CaseValuesAttrVerifyErr(
                    pair[0].get_type().disp(ctx).to_string(),
                    pair[1].get_type().disp(ctx).to_string()
                ))
            } else {
                Ok(())
            }
        })
    }
}

pub fn register(ctx: &mut Context) {
    IntegerOverflowFlagsAttr::register_attr_in_dialect(ctx, IntegerOverflowFlagsAttr::parser_fn);
    ICmpPredicateAttr::register_attr_in_dialect(ctx, ICmpPredicateAttr::parser_fn);
    FCmpPredicateAttr::register_attr_in_dialect(ctx, FCmpPredicateAttr::parser_fn);
    GepIndicesAttr::register_attr_in_dialect(ctx, GepIndicesAttr::parser_fn);
    CaseValuesAttr::register_attr_in_dialect(ctx, CaseValuesAttr::parser_fn);
    InsertExtractValueIndicesAttr::register_attr_in_dialect(
        ctx,
        InsertExtractValueIndicesAttr::parser_fn,
    );
    FastmathFlagsAttr::register_attr_in_dialect(ctx, FastmathFlagsAttr::parser_fn);
}

#[def_attribute("llvm.insert_extract_value_indices")]
#[format_attribute("`[` vec($0, CharSpace(`,`)) `]`")]
#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct InsertExtractValueIndicesAttr(pub Vec<u32>);
impl_verify_succ!(InsertExtractValueIndicesAttr);

#[cfg(test)]
mod tests {
    use expect_test::expect;
    use pliron::{
        location,
        parsable::{self, state_stream_from_iterator},
    };

    use super::*;

    #[test]
    fn test_fastmath_flags_attr_default() {
        let flags = FastmathFlags::default();
        assert_eq!(flags.bits(), 0);
    }

    #[test]
    fn test_fastmath_flags_attr_set_flags() {
        let mut flags = FastmathFlags::empty();
        flags |= FastmathFlags::NNAN | FastmathFlags::NINF;
        assert!(flags.contains(FastmathFlags::NNAN));
        assert!(flags.contains(FastmathFlags::NINF));
        assert!(!flags.contains(FastmathFlags::NSZ));
    }

    #[test]
    fn test_fastmath_flags_attr_fmt() {
        let ctx = &Context::default();
        let flags: FastmathFlagsAttr = (FastmathFlags::NNAN | FastmathFlags::ARCP).into();
        expect!["<NNAN | ARCP>"].assert_eq(&flags.disp(ctx).to_string());
    }

    #[test]
    fn test_fastmath_flags_attr_fmt_fast() {
        let ctx = &Context::default();
        let flags: FastmathFlagsAttr = FastmathFlags::FAST.into();
        expect!["<NNAN | NINF | NSZ | ARCP | CONTRACT | AFN | REASSOC>"]
            .assert_eq(&flags.disp(ctx).to_string());
    }

    #[test]
    fn test_fastmath_flags_attr_parse_valid() {
        let ctx = &mut Context::default();

        let input = "<NNAN | ARCP>";
        let mut state_stream = state_stream_from_iterator(
            input.chars(),
            parsable::State::new(ctx, location::Source::InMemory),
        );
        let (parsed, _) = FastmathFlagsAttr::parse(&mut state_stream, ()).unwrap();
        assert!(parsed.0.contains(FastmathFlags::NNAN));
        assert!(parsed.0.contains(FastmathFlags::ARCP));
    }

    // Test input with FAST flag set
    #[test]
    fn test_fastmath_flags_attr_parse_fast() {
        let ctx = &mut Context::default();

        let input = "<FAST>";
        let mut state_stream = state_stream_from_iterator(
            input.chars(),
            parsable::State::new(ctx, location::Source::InMemory),
        );
        let (parsed, _) = FastmathFlagsAttr::parse(&mut state_stream, ()).unwrap();
        assert!(parsed.0.contains(FastmathFlags::FAST));

        // FAST also means all the other flags.
        assert!(parsed.0.contains(FastmathFlags::NNAN));
        assert!(parsed.0.contains(FastmathFlags::NINF));
        assert!(parsed.0.contains(FastmathFlags::NSZ));
        assert!(parsed.0.contains(FastmathFlags::ARCP));
        assert!(parsed.0.contains(FastmathFlags::CONTRACT));
        assert!(parsed.0.contains(FastmathFlags::REASSOC));
    }

    #[test]
    fn test_fastmath_flags_attr_parse_invalid() {
        let ctx = &mut Context::default();
        let input = "<INVALIDFLAG>";
        let state_stream = state_stream_from_iterator(
            input.chars(),
            parsable::State::new(ctx, location::Source::InMemory),
        );
        match FastmathFlagsAttr::parser(()).parse(state_stream) {
            Ok((parsed, _)) => {
                panic!("Expected error, but got: {}", parsed);
            }
            Err(e) => {
                expect![[r#"
                    Parse error at line: 1, column: 1
                    Error parsing fastmath flags: unrecognized named flag `INVALIDFLAG`
                "#]]
                .assert_eq(&e.to_string());
            }
        }
    }
}
