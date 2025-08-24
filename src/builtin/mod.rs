//! Builtin dialect: [Op](crate::op::Op)s, [Type](crate::type::Type)s and [Attribute](crate::attribute::Attribute)s

pub mod attr_interfaces;
pub mod attributes;
pub mod op_interfaces;
pub mod ops;
pub mod type_interfaces;
pub mod types;

use crate::{
    context::Context,
    dialect::{Dialect, DialectName},
    dict_key,
};

pub fn register(ctx: &mut Context) {
    let dialect = Dialect::new(DialectName::new("builtin"));
    dialect.register(ctx);
    ops::register(ctx);
    types::register(ctx);
    attributes::register(ctx);
}

dict_key!(
    /// Key for debug info related attributes.
    ATTR_KEY_DEBUG_INFO, "builtin_debug_info"
);
