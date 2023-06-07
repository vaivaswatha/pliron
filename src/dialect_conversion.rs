use crate::context::Context;
use crate::context::Ptr;
use crate::error::CompilerError;
use crate::operation::Operation;
use crate::pass::ConversionTarget;
use crate::pattern_match::AccumulatingListener;
use crate::pattern_match::GenericPatternRewriter;
use crate::rewrite::PatternApplicator;
use crate::rewrite::RewritePatternSet;

pub fn apply_partial_conversion(
    ctx: &mut Context,
    _op: Ptr<Operation>,
    _target: &ConversionTarget,
    pattern_set: RewritePatternSet,
) -> Result<(), CompilerError> {
    let to_convert: Vec<Ptr<Operation>> = vec![];
    // TODO: walk the operation by calling the callback on each nested operation and fill to_convert
    let listener = Box::new(AccumulatingListener::new());
    let mut rewriter = GenericPatternRewriter::new(Some(listener));
    let applicatior = PatternApplicator::new(pattern_set);
    for op_to_convert in to_convert.iter() {
        // TODO: if the operation is legal, skip it, if not legalize by running the pattern set on it
        applicatior.match_and_rewrite::<GenericPatternRewriter>(
            ctx,
            *op_to_convert,
            &mut rewriter,
        )?;
    }
    // TODO: legalize newly inserted/replaced operations
    Ok(())
}
