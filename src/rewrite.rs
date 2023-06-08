use crate::context::Context;
use crate::context::Ptr;
use crate::error::CompilerError;
use crate::operation::Operation;
use crate::pattern_match::MatchResult;
use crate::pattern_match::PatternRewriter;
use crate::pattern_match::RewritePattern;

/// This class manages the application of a group of rewrite patterns, with a
/// user-provided cost model.
pub struct PatternApplicator {
    patterns: RewritePatternSet,
}

impl PatternApplicator {
    pub fn new(patterns: RewritePatternSet) -> Self {
        Self { patterns }
    }

    /// Attempt to match and rewrite the given op with any pattern, allowing a
    /// predicate to decide if a pattern can be applied or not, and hooks for if
    /// the pattern match was a success or failure.
    ///
    /// canApply:  called before each match and rewrite attempt; return false to
    ///            skip pattern.
    /// onFailure: called when a pattern fails to match to perform cleanup.
    /// onSuccess: called when a pattern match succeeds;
    pub fn match_and_rewrite<R: PatternRewriter>(
        &self,
        ctx: &mut Context,
        op: Ptr<Operation>,
        rewriter: &mut dyn PatternRewriter,
        // TODO:
        //   function_ref<bool(const Pattern &)> canApply = {},
        //   function_ref<void(const Pattern &)> onFailure = {},
        //   function_ref<LogicalResult(const Pattern &)> onSuccess = {});
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

/// A set of patterns that can be applied to an operation.
#[derive(Default)]
pub struct RewritePatternSet {
    /// The patterns in this set.
    pub patterns: Vec<Box<dyn RewritePattern>>,
}

impl RewritePatternSet {
    pub fn add(&mut self, pattern: Box<dyn RewritePattern>) {
        self.patterns.push(pattern);
    }
}
