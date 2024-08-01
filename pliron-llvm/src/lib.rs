//! LLVM Dialect for [pliron]

use pliron::{
    context::Context,
    dialect::{Dialect, DialectName},
};

pub mod attributes;
pub mod from_llvm_ir;
pub mod llvm_sys;
pub mod op_interfaces;
pub mod ops;
pub mod to_llvm_ir;
pub mod types;

/// Register LLVM dialect, its ops, types and attributes into context.
pub fn register(ctx: &mut Context) {
    let dialect = Dialect::new(DialectName::new("llvm"));
    dialect.register(ctx);
    ops::register(ctx);
    types::register(ctx);
}
