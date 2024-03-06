mod attrs;
mod ops;
mod types;

pub use attrs::*;
pub use ops::*;
use pliron::{
    context::Context,
    dialect::{Dialect, DialectName},
};
pub use types::*;

pub fn register(ctx: &mut Context) {
    let mut dialect = Dialect::new(DialectName::new("kal"));
    types::register(&mut dialect);
    attrs::register(&mut dialect);
    ops::register(ctx, &mut dialect);
    dialect.register(ctx);
}
