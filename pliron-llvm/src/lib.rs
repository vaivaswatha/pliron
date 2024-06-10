//! LLVM Dialect for [pliron]

use pliron::{
    context::Context,
    dialect::{Dialect, DialectName},
};

pub mod attributes;
pub mod from_inkwell;
pub mod op_interfaces;
pub mod ops;
pub mod types;

/// Register LLVM dialect, its ops, types and attributes into context.
pub fn register(ctx: &mut Context) {
    let dialect = Dialect::new(DialectName::new("llvm"));
    dialect.register(ctx);
    ops::register(ctx);
    types::register(ctx);
}
