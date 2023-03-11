pub mod attributes;
pub mod ops;
pub mod properties;
pub mod types;

use crate::{
    context::Context,
    dialect::{Dialect, DialectName},
};

pub fn register(ctx: &mut Context) {
    let mut dialect = Dialect::new(DialectName::new("builtin"));
    ops::register(ctx, &mut dialect);
    types::register(&mut dialect);
    attributes::register(&mut dialect);
}
