use std::vec;

use rustc_hash::FxHashMap;
use thiserror::Error;

use crate::context::Context;
use crate::context::Ptr;
use crate::dialect::Dialect;
use crate::dialect::DialectName;
use crate::op::Op;
use crate::op::OpId;
use crate::operation::Operation;
use crate::operation::WalkOrder;
use crate::operation::WalkResut;
use crate::pattern_match::AccumulatingListener;
use crate::pattern_match::GenericPatternRewriter;
use crate::pattern_match::PatternRewriter;
use crate::pattern_match::PatternRewriterError;
use crate::rewrite::PatternApplicator;
use crate::rewrite::RewritePatternSet;
use crate::with_context::AttachContext;

/// This enumeration corresponds to the specific action to take when
/// considering an operation legal for this conversion target.
pub enum LegalizationAction {
    /// The target supports this operation.
    Legal,

    /// This operation has dynamic legalization constraints that must be checked
    /// by the target.
    Dynamic,

    /// The target explicitly does not support this operation.
    Illegal,
}

#[derive(Default)]
pub struct ConversionTarget {
    legal_dialects: FxHashMap<DialectName, LegalizationAction>,
    illegal_dialects: FxHashMap<DialectName, LegalizationAction>,
}

impl ConversionTarget {
    fn set_op_action(&mut self, _op_id: OpId, _action: LegalizationAction) {
        todo!()
    }

    pub fn add_legal_dialect(&mut self, dialect: &Dialect) {
        self.legal_dialects
            .entry(dialect.get_name().clone())
            .or_insert(LegalizationAction::Legal);
    }
    pub fn add_illegal_dialect(&mut self, dialect: &Dialect) {
        self.illegal_dialects
            .entry(dialect.get_name().clone())
            .or_insert(LegalizationAction::Illegal);
    }
    pub fn add_dynamically_legal_op<OpT: Op>(&mut self, _callback: fn(Ptr<Operation>) -> bool) {
        self.set_op_action(OpT::get_opid_static(), LegalizationAction::Dynamic);
        todo!("set legality callback");
    }

    pub fn is_legal(&self, ctx: &Context, op: Ptr<Operation>) -> LegalOpDetails {
        let dialect_name = op.deref(ctx).get_opid().dialect;
        if self.legal_dialects.contains_key(&dialect_name) {
            LegalOpDetails::Legal {
                is_recursively_legal: false,
            }
        } else {
            LegalOpDetails::Illegal
        }
    }
}

/// A structure containing additional information describing a specific legal
/// operation instance.
pub enum LegalOpDetails {
    Illegal,
    Legal {
        /// A flag that indicates if this operation is 'recursively' legal. This
        /// means that if an operation is legal, either statically or dynamically,
        /// all of the operations nested within are also considered legal.
        is_recursively_legal: bool,
    },
    Unknown,
}

impl LegalOpDetails {
    pub fn is_legal(&self) -> bool {
        match self {
            LegalOpDetails::Illegal => false,
            LegalOpDetails::Legal {
                is_recursively_legal: _,
            } => true,
            LegalOpDetails::Unknown => false,
        }
    }
}

#[derive(Debug, Error)]
enum LegalizationError {
    #[error("Legalization failed. RewritePattern error: {0}")]
    RewritePatternError(#[from] PatternRewriterError),
    #[error("Legalization failed: {msg}")]
    Failure { msg: String },
}

struct OperationLegalizer {
    target: ConversionTarget,
    applicator: PatternApplicator,
}

impl OperationLegalizer {
    fn new(target: ConversionTarget, patterns: RewritePatternSet) -> Self {
        Self {
            target,
            applicator: PatternApplicator::new(patterns),
        }
    }

    fn legalize(
        &self,
        ctx: &mut Context,
        op: Ptr<Operation>,
        rewriter: &mut dyn PatternRewriter,
    ) -> Result<(), LegalizationError> {
        match self.target.is_legal(ctx, op) {
            LegalOpDetails::Illegal => (),
            LegalOpDetails::Legal {
                is_recursively_legal,
            } => {
                if is_recursively_legal {
                    // TODO: If this operation is recursively legal, mark its children as ignored so
                    // that we don't consider them for legalization.
                }
                return Ok(());
            }
            LegalOpDetails::Unknown => (),
        };
        // TODO: Check to see if the operation is ignored and doesn't need to be converted.
        self.legalize_with_pattern(ctx, op, rewriter)
    }

    fn legalize_with_pattern(
        &self,
        ctx: &mut Context,
        op: Ptr<Operation>,
        rewriter: &mut dyn PatternRewriter,
    ) -> Result<(), LegalizationError> {
        if !self.applicator.match_and_rewrite(ctx, op, rewriter)? {
            return Err(LegalizationError::Failure {
                msg: format!(
                    "match_and_rewrite failed on operation: {:?}",
                    op.with_ctx(ctx).to_string()
                ),
            });
        }
        Ok(())
    }

    pub fn is_illegal(&self, ctx: &Context, op: Ptr<Operation>) -> bool {
        !self.target.is_legal(ctx, op).is_legal()
    }
}

/// Apply rewrite patterns to the op and all it's nested operations until there is no
/// illegal operations left as set by the conversion target.
pub fn apply_partial_conversion(
    ctx: &mut Context,
    op: Ptr<Operation>,
    target: ConversionTarget,
    pattern_set: RewritePatternSet,
) -> Result<(), ConversionError> {
    let op_convertor = OperationConverter::new(target, pattern_set, OpConversionMode::Partial);
    op_convertor.convert_operations(ctx, vec![op])?;
    // TODO: legalize newly inserted/replaced operations
    Ok(())
}

pub enum OpConversionMode {
    /// In this mode, the conversion will ignore failed conversions to allow
    /// illegal operations to co-exist in the IR.
    Partial,

    /// In this mode, all operations must be legal for the given target for the
    /// conversion to succeed.
    Full,

    /// In this mode, operations are analyzed for legality. No actual rewrites are
    /// applied to the operations on success.
    Analysis,
}

#[derive(Debug, Error)]
pub enum ConversionError {
    #[error("Conversion failed. Failed to legilize {failed_op} with error: {orig_error_msg}")]
    FailedToLegalize {
        orig_error_msg: String,
        failed_op: String,
    },
}

struct OperationConverter {
    legalizer: OperationLegalizer,
    mode: OpConversionMode,
}

impl OperationConverter {
    fn new(
        target: ConversionTarget,
        pattern_set: RewritePatternSet,
        mode: OpConversionMode,
    ) -> Self {
        Self {
            legalizer: OperationLegalizer::new(target, pattern_set),
            mode,
        }
    }

    fn convert_operations(
        &self,
        ctx: &mut Context,
        ops: Vec<Ptr<Operation>>,
    ) -> Result<(), ConversionError> {
        let target = &self.legalizer.target;
        let mut to_convert: Vec<Ptr<Operation>> = vec![];
        for op in ops {
            op.walk(ctx, WalkOrder::PostOrder, &mut |op| {
                to_convert.push(op);
                match target.is_legal(ctx, op) {
                    LegalOpDetails::Legal {
                        is_recursively_legal,
                    } if is_recursively_legal => WalkResut::Skip,
                    _ => WalkResut::Advance,
                }
            });
        }
        let listener = Box::<AccumulatingListener>::default();
        let mut rewriter = GenericPatternRewriter::new(Some(listener));
        for op in to_convert.into_iter() {
            // TODO: check if the op is not yet erased/unlinked
            // (think module op pass that erases/swaps nested ops)
            // TODO: if the operation is legal, skip it, if not, legalize by running the pattern set on it
            self.convert(ctx, op, &mut rewriter)?;
        }

        Ok(())
    }

    fn convert(
        &self,
        ctx: &mut Context,
        op: Ptr<Operation>,
        rewriter: &mut dyn PatternRewriter,
    ) -> Result<(), ConversionError> {
        let res = self.legalizer.legalize(ctx, op, rewriter);
        if let Err(err) = res {
            match self.mode {
                // Partial conversions allow conversions to fail if the operation was not
                // explicitly marked as illegal.
                OpConversionMode::Partial => {
                    if self.legalizer.is_illegal(ctx, op) {
                        return Err(ConversionError::FailedToLegalize {
                            orig_error_msg: err.to_string(),
                            failed_op: op.with_ctx(ctx).to_string(),
                        });
                    }
                }
                OpConversionMode::Full => Err(ConversionError::FailedToLegalize {
                    orig_error_msg: err.to_string(),
                    failed_op: op.with_ctx(ctx).to_string(),
                })?,
                OpConversionMode::Analysis => todo!(),
            }
        }
        Ok(())
    }
}
