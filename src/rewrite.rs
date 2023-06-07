use crate::context::Context;
use crate::context::Ptr;
use crate::error::CompilerError;
use crate::operation::Operation;
use crate::pattern_match::MatchResult;
use crate::pattern_match::OpRewritePattern;
use crate::pattern_match::PatternRewriter;

/// from MLIR's PatternApplicator:
/// This class manages the application of a group of rewrite patterns, with a
/// user-provided cost model.
pub struct PatternApplicator {
    patterns: RewritePatternSet,
}

impl PatternApplicator {
    pub fn new(patterns: RewritePatternSet) -> Self {
        Self { patterns }
    }

    // TODO: use PatternRewriter instead of GenericPatternRewriter
    pub fn match_and_rewrite<R: PatternRewriter>(
        &self,
        ctx: &mut Context,
        op: Ptr<Operation>,
        rewriter: &mut dyn PatternRewriter,
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

pub struct RewritePatternSet {
    /// The set of patterns to match against.
    pub patterns: Vec<Box<dyn OpRewritePattern>>,
}

impl<'a> RewritePatternSet {
    pub fn new() -> Self {
        Self { patterns: vec![] }
    }

    pub fn add(&mut self, pattern: Box<dyn OpRewritePattern>) {
        self.patterns.push(pattern);
    }
}
