use rustc_hash::FxHashMap;

use crate::context::Context;
use crate::context::Ptr;
use crate::dialect::Dialect;
use crate::dialect::DialectName;
use crate::error::CompilerError;
use crate::op::Op;
use crate::op::OpId;
use crate::operation::Operation;
use crate::operation::WalkOrder;
use crate::operation::WalkResut;
use crate::pattern_match::AccumulatingListener;
use crate::pattern_match::GenericPatternRewriter;
use crate::rewrite::PatternApplicator;
use crate::rewrite::RewritePatternSet;

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
}

impl ConversionTarget {
    pub fn new() -> Self {
        Self {
            legal_dialects: FxHashMap::default(),
        }
    }

    pub fn add_legal_dialect(&mut self, dialect: &Dialect) {
        self.legal_dialects
            .entry(dialect.get_name().clone())
            .or_insert(LegalizationAction::Legal);
    }
    pub fn add_illegal_dialect(&mut self, dialect: &Dialect) {
        self.legal_dialects
            .entry(dialect.get_name().clone())
            .or_insert(LegalizationAction::Illegal);
    }
    pub fn add_dynamically_legal_op<OpT: Op>(&mut self, _callback: fn(Ptr<Operation>) -> bool) {
        self.set_op_action(OpT::get_opid_static(), LegalizationAction::Dynamic);
        todo!("set legality callback");
    }
    fn set_op_action(&mut self, _op_id: OpId, _action: LegalizationAction) {
        todo!()
    }
}

/// Apply rewrite patterns to the op and all it's nested operations until there is no
/// illegal operations left as set by the conversion target.
pub fn apply_partial_conversion(
    ctx: &mut Context,
    op: Ptr<Operation>,
    _target: &ConversionTarget,
    pattern_set: RewritePatternSet,
) -> Result<(), CompilerError> {
    let mut to_convert: Vec<Ptr<Operation>> = vec![];
    op.walk(ctx, WalkOrder::PostOrder, &mut |op| {
        to_convert.push(op);
        // TODO: Don't check this operation's children for conversion if the operation is recursively legal.
        WalkResut::Advance
    });
    let listener = Box::<AccumulatingListener>::default();
    let mut rewriter = GenericPatternRewriter::new(Some(listener));
    let applicatior = PatternApplicator::new(pattern_set);
    for op_to_convert in to_convert.iter() {
        // TODO: if the operation is legal, skip it, if not, legalize by running the pattern set on it
        applicatior.match_and_rewrite::<GenericPatternRewriter>(
            ctx,
            *op_to_convert,
            &mut rewriter,
        )?;
    }
    // TODO: legalize newly inserted/replaced operations
    Ok(())
}
