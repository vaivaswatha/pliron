//! Utilites for matching operations and rewriting them.
//! Similar in spirit to MLIR's pattern matching rewrites.

use std::collections::VecDeque;

use rustc_hash::FxHashSet;

use crate::{
    context::{Context, Ptr},
    graph::walkers::{IRNode, WALKCONFIG_PREORDER_FORWARD, immutable::walk_op},
    irbuild::{
        inserter::{Inserter, OpInsertionPoint},
        listener::{Recorder, RecorderEvent},
        rewriter::IRRewriter,
    },
    operation::Operation,
    result::Result,
};

/// A rewriter that uses the [Recorder] listener.
pub type MatchRewriter = IRRewriter<Recorder>;

/// Interface for matching and rewriting operations.
pub trait MatchRewrite {
    /// Should operation be rewritten?
    fn r#match(&mut self, ctx: &Context, op: Ptr<Operation>) -> bool;
    /// Rewrite the matched operation.
    /// Insertion point is set to be before the operation being rewritten.
    fn rewrite(
        &mut self,
        ctx: &mut Context,
        rewriter: &mut MatchRewriter,
        op: Ptr<Operation>,
    ) -> Result<()>;
}

/// Collects all operations (recursively) that match a given pattern
/// and then applies a rewrite to them.
pub fn collect_rewrite<M: MatchRewrite>(
    ctx: &mut Context,
    mut match_rewrite: M,
    op: Ptr<Operation>,
) -> Result<()> {
    let mut to_rewrite = VecDeque::new();

    // Collect all operations that match.
    struct WalkerState<'a, M> {
        match_rewrite: &'a mut M,
        to_rewrite: &'a mut VecDeque<Ptr<Operation>>,
    }
    let mut state = WalkerState {
        match_rewrite: &mut match_rewrite,
        to_rewrite: &mut to_rewrite,
    };
    // A callback for the walker.
    fn walker_callback<M: MatchRewrite>(ctx: &Context, state: &mut WalkerState<M>, node: IRNode) {
        if let IRNode::Operation(op) = node
            && state.match_rewrite.r#match(ctx, op)
        {
            state.to_rewrite.push_back(op);
        }
    }
    // Walk the operation tree.
    walk_op(
        ctx,
        &mut state,
        &WALKCONFIG_PREORDER_FORWARD,
        op,
        walker_callback,
    );

    let mut erased = FxHashSet::<Ptr<Operation>>::default();
    let mut rewriter = MatchRewriter::default();
    rewriter.set_listener(Recorder::default());

    // Rewrite collected and newly added operations that match.
    while !to_rewrite.is_empty() {
        let op = to_rewrite.pop_front().unwrap();
        if erased.contains(&op) {
            continue;
        }
        rewriter.set_insertion_point(OpInsertionPoint::BeforeOperation(op));
        match_rewrite.rewrite(ctx, &mut rewriter, op)?;
        let listener = rewriter
            .get_listener_mut()
            .expect("Rewriter must have a listener attached");
        for event in &listener.events {
            match event {
                RecorderEvent::ErasedOperation(erased_op) => {
                    erased.insert(*erased_op);
                }
                RecorderEvent::InsertedOperation(_new_op) => {
                    // Check if the newly inserted operation also matches.
                    if match_rewrite.r#match(ctx, *_new_op) {
                        to_rewrite.push_back(*_new_op);
                    }
                }
                RecorderEvent::ReplacedOperation { .. } => {
                    // No action needed for replacements.
                }
                RecorderEvent::CreatedBlock(_) => {
                    // No action needed for block creations.
                }
            }
        }
        listener.clear();
    }
    Ok(())
}
