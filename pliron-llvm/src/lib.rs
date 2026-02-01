//! LLVM Dialect for [pliron]

use pliron::{
    context::Context, derive::op_interface, irbuild::match_rewrite::MatchRewriter, op::Op,
    result::Result,
};

pub mod attributes;
pub mod from_llvm_ir;
pub mod llvm_sys;
pub mod op_interfaces;
pub mod ops;
pub mod to_llvm_ir;
pub mod types;

/// Interface for rewriting to LLVM dialect.
#[op_interface]
pub trait ToLLVMDialect {
    /// Rewrite [self] to LLVM dialect.
    fn rewrite(&self, ctx: &mut Context, rewriter: &mut MatchRewriter) -> Result<()>;

    fn verify(_op: &dyn Op, _ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        Ok(())
    }
}
