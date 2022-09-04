use crate::{
    context::Context,
    dialect::{Dialect, DialectName},
};

pub mod ops;
pub mod types;

pub fn register(ctx: &mut Context) {
    let mut dialect = Dialect::new(DialectName::new("llvm"));
    ops::register(ctx, &mut dialect);
}
