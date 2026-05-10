//! Dead code elimination
//!
//! This pass removes operations that satisfy both the following conditions:
//! 1. The operation has no side effects.
//! 2. The operation's (SSA) results are not used by any other operation.
//!
//! An operation is considered to have side effects if either:
//! 1. It does not implement the [SideEffects] interface, or
//! 2. It implements the [SideEffects] interface and returns
//!    `true` for the `has_side_effects` method.

use pliron_derive::op_interface;
use rustc_hash::FxHashSet;

use crate::{
    context::{Context, Ptr},
    graph::walkers::{WALKCONFIG_PREORDER_FORWARD, uninterruptible::mutable::walk_op},
    irbuild::{
        listener::{DummyListener, RewriteListener},
        rewriter::{IRRewriter, Rewriter},
    },
    op::{Op, op_cast},
    operation::{OpDbg, Operation},
    opts::OptStatus,
    result::Result,
    value::Value,
};

/// Convey the presence of side effects in an operation.
#[op_interface]
pub trait SideEffects {
    /// Returns `true` if the operation has side effects, and `false` otherwise.
    fn has_side_effects(&self, ctx: &Context) -> bool;

    // Generally there's nothing to verify here. Can be overrided.
    fn verify(_op: &dyn Op, _ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        Ok(())
    }
}

/// Can this operation be safely removed as per our DCE criteria?
fn is_safe_to_erase(op: Ptr<Operation>, ctx: &Context) -> bool {
    let op_ref = op.deref(ctx);

    // Get the dynamic op interface to check for SideEffects
    let op_dyn = Operation::get_op_dyn(op, ctx);

    // Determine if operation has side effects
    let has_side_effects = match op_cast::<dyn SideEffects>(&*op_dyn) {
        Some(side_effects_op) => side_effects_op.has_side_effects(ctx),
        None => true, // If it doesn't implement SideEffects, assume it has side effects
    };

    // Check if all results are unused
    let all_results_unused = !op_ref.has_use();

    !has_side_effects && all_results_unused
}

/// Perform dead code elimination on the given operation and its nested operations, using the provided rewriter.
pub fn dce_with_rewriter<L: RewriteListener>(
    op: Ptr<Operation>,
    ctx: &mut Context,
    rewriter: &mut IRRewriter<L>,
) -> Result<OptStatus> {
    let mut cemetery: Vec<Ptr<Operation>> = Vec::new();

    // Step 1: Recursively walk the operation tree to collect all dead operations
    walk_op(
        ctx,
        &mut cemetery,
        &WALKCONFIG_PREORDER_FORWARD,
        op,
        |ctx, cemetery, ir_node| {
            if let crate::graph::walkers::IRNode::Operation(curr_op) = ir_node
                && is_safe_to_erase(curr_op, ctx)
            {
                cemetery.push(curr_op);
            }
        },
    );

    // Step 2: Process the cemetery (dead operations)
    let mut modified = OptStatus::IRUnchanged;

    while let Some(dead_op) = cemetery.pop() {
        // Collect defining operations before erasing this one
        let defining_ops: FxHashSet<Ptr<Operation>> = dead_op
            .deref(ctx)
            .operands()
            .filter_map(|opd| {
                if let Value::OpResult {
                    op: def_op,
                    val_uid: _,
                } = opd
                {
                    Some(def_op)
                } else {
                    // We don't eliminate block arguments yet.
                    None
                }
            })
            .collect();

        // Erase the dead operation
        log::trace!("Erasing dead operation: {}", OpDbg { op: dead_op, ctx });
        rewriter.erase_operation(ctx, dead_op);
        modified = OptStatus::IRChanged;

        // For each operand, check if the defining operation is now dead
        for def_op in defining_ops {
            // If no side effects, add to cemetery for processing
            if is_safe_to_erase(def_op, ctx) {
                cemetery.push(def_op);
            }
        }
    }

    Ok(modified)
}

/// Perform dead code elimination on the given operation and its nested operations.
pub fn dce(op: Ptr<Operation>, ctx: &mut Context) -> Result<OptStatus> {
    let mut rewriter = IRRewriter::<DummyListener>::default();
    dce_with_rewriter(op, ctx, &mut rewriter)
}
