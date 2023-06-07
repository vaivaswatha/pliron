use crate::context::Context;
use crate::context::Ptr;
use crate::error::CompilerError;
use crate::operation::Operation;
use crate::pattern_match::Listener;
use crate::pattern_match::MatchResult;
use crate::pattern_match::OpRewritePattern;
use crate::pattern_match::PatternRewriter;

/// from MLIR's PatternApplicator:
/// This class manages the application of a group of rewrite patterns, with a
/// user-provided cost model.
pub struct PatternApplicator<'a, L: Listener> {
    patterns: RewritePatternSet<'a, L>,
}

impl<'a, L: Listener> PatternApplicator<'a, L> {
    pub fn new(patterns: RewritePatternSet<'a, L>) -> Self {
        Self { patterns }
    }

    // TODO: use PatternRewriter instead of GenericPatternRewriter
    pub fn match_and_rewrite<R: PatternRewriter<'a, L>>(
        &self,
        ctx: &mut Context,
        op: Ptr<Operation>,
        rewriter: &'a mut dyn PatternRewriter<'a, L>,
    ) -> Result<MatchResult, CompilerError> {
        let mut matched = MatchResult::Fail;
        for pattern in self.patterns.patterns.iter() {
            rewriter.set_insertion_point(op);
            matched = pattern.match_and_rewrite(ctx, op, rewriter)?;
            if matched.is_success() {
                break;
            }
        }
        Ok(matched)
    }
}

pub struct RewritePatternSet<'a, L: Listener> {
    /// The set of patterns to match against.
    pub patterns: Vec<Box<dyn OpRewritePattern<'a, L>>>,
}

impl<'a, L: Listener> RewritePatternSet<'a, L> {
    pub fn new() -> Self {
        Self { patterns: vec![] }
    }

    pub fn add(&mut self, pattern: Box<dyn OpRewritePattern<'a, L>>) {
        self.patterns.push(pattern);
    }
}
