use crate::context::Context;
use crate::context::Ptr;
use crate::operation::Operation;
use crate::pattern_match::PatternRewriter;
use crate::pattern_match::PatternRewriterError;
use crate::pattern_match::RewritePattern;

/// This class manages the application of a group of rewrite patterns
pub struct PatternApplicator {
    patterns: RewritePatternSet,
}

impl PatternApplicator {
    pub fn new(patterns: RewritePatternSet) -> Self {
        Self { patterns }
    }

    /// Attempt to match and rewrite the given op with any pattern.
    /// Returns true if any pattern matched the op or false if none did.
    pub fn match_and_rewrite(
        &self,
        ctx: &mut Context,
        op: Ptr<Operation>,
        rewriter: &mut dyn PatternRewriter,
    ) -> Result<bool, PatternRewriterError> {
        for pattern in self.patterns.patterns.iter() {
            rewriter.set_insertion_point(op);
            if pattern.match_and_rewrite(ctx, op, rewriter).map_err(|e| {
                PatternRewriterError::PatternFailed {
                    error: e,
                    pattern_name: pattern.name(),
                }
            })? {
                return Ok(true);
            }
        }
        Ok(false)
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
