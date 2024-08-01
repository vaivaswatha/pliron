//! Builtin dialect: [Op](crate::op::Op)s, [Type](crate::type::Type)s and [Attribute](crate::attribute::Attribute)s

pub mod attr_interfaces;
pub mod attributes;
pub mod op_interfaces;
pub mod ops;
pub mod types;

use std::sync::LazyLock;

use crate::{
    context::Context,
    dialect::{Dialect, DialectName},
    identifier::Identifier,
};

pub fn register(ctx: &mut Context) {
    let dialect = Dialect::new(DialectName::new("builtin"));
    dialect.register(ctx);
    ops::register(ctx);
    types::register(ctx);
    attributes::register(ctx);
}

/// Key for debug info related attributes.
pub static ATTR_KEY_DEBUG_INFO: LazyLock<Identifier> =
    LazyLock::new(|| "builtin_debug_info".try_into().unwrap());
