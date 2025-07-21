//! Attributes belonging to the LLVM dialect.

use pliron::attribute::Attribute;
use pliron::builtin::attributes::IntegerAttr;
use pliron::common_traits::Verify;
use pliron::context::Context;
use pliron::derive::{def_attribute, format, format_attribute};
use pliron::printable::Printable;
use pliron::result::Result;

use pliron::parsable::Parsable;
use pliron::{impl_verify_succ, verify_err_noloc};
use thiserror::Error;

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
    GepIndicesAttr::register_attr_in_dialect(ctx, GepIndicesAttr::parser_fn);
}

#[def_attribute("llvm.insert_extract_value_indices")]
#[format_attribute("`[` vec($0, CharSpace(`,`)) `]`")]
#[derive(PartialEq, Eq, Clone, Debug, Hash)]
pub struct InsertExtractValueIndicesAttr(pub Vec<u32>);
impl_verify_succ!(InsertExtractValueIndicesAttr);
