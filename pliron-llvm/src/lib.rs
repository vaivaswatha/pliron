use pliron::{
    context::Context,
    dialect::{Dialect, DialectName},
};

pub mod attributes;
pub mod op_interfaces;
pub mod ops;
pub mod types;

pub fn register(ctx: &mut Context) {
    let dialect = Dialect::new(DialectName::new("llvm"));
    dialect.register(ctx);
    ops::register(ctx);
    types::register(ctx);
}
