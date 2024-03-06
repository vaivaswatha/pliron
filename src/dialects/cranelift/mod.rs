pub mod attributes;
pub mod ops;
pub mod types;

use crate::{
    context::Context,
    dialect::{Dialect, DialectName},
};

pub fn register(ctx: &mut Context) {
    let mut dialect = Dialect::new(DialectName::new("cranelift"));
    attributes::register(&mut dialect);
    ops::register(ctx, &mut dialect);
    types::register(&mut dialect);
    dialect.register(ctx);
}
