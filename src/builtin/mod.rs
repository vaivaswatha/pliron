pub mod attr_interfaces;
pub mod attributes;
pub mod op_interfaces;
pub mod ops;
pub mod types;

use crate::{
    context::Context,
    dialect::{Dialect, DialectName},
};

pub fn register(ctx: &mut Context) {
    let dialect = Dialect::new(DialectName::new("builtin"));
    dialect.register(ctx);
    ops::register(ctx);
    types::register(ctx);
    attributes::register(ctx);
}

/// Key for debug info related attributes.
pub const ATTR_KEY_DEBUG_INFO: &str = "builtin.debug_info";
