use pliron::{
    context::Context,
    dialect::{Dialect, DialectName},
};

pub mod attributes;
pub mod op_interfaces;
pub mod ops;
pub mod types;

pub fn register(ctx: &mut Context) {
    let mut dialect = Dialect::new(DialectName::new("llvm"));
    ops::register(ctx, &mut dialect);
    types::register(&mut dialect);
    dialect.register(ctx);
}
