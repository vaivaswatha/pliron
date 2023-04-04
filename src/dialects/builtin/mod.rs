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
    let mut dialect = Dialect::new(DialectName::new("builtin"));
    ops::register(ctx, &mut dialect);
    types::register(&mut dialect);
    attributes::register(&mut dialect);
}

/// Key for debug info related attributes.
pub const ATTR_KEY_DEBUG_INFO: &str = "builtin.debug_info";
/// Key for symbol name attribute, if the operation defines a symbol.
pub const ATTR_KEY_SYM_NAME: &str = "builtin.sym_name";
