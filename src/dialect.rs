use std::ops::Deref;

use crate::{
    attribute::AttrId, common_traits::DisplayWithContext, context::Context, op::OpId,
    r#type::TypeId, with_context::AttachContext,
};

/// Dialect name: Safe wrapper around a String.
#[derive(Clone, Hash, PartialEq, Eq)]
pub struct DialectName(String);

impl DialectName {
    /// Create a new DialectName
    pub fn new(name: &str) -> DialectName {
        DialectName(name.to_string())
    }
}

impl AttachContext for DialectName {}
impl DisplayWithContext for DialectName {
    fn fmt(&self, _ctx: &Context, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Deref for DialectName {
    type Target = String;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// A collection of Types and Ops.
/// Dialects are identified by their names.
pub struct Dialect {
    /// Name of this dialect.
    name: DialectName,
    /// Ops that are part of this dialect.
    ops: Vec<OpId>,
    /// Types that are part of this dialect.
    types: Vec<TypeId>,
    /// Attributes that are part of this dialect.
    attributes: Vec<AttrId>,
}

impl AttachContext for Dialect {}
impl DisplayWithContext for Dialect {
    fn fmt(&self, ctx: &Context, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.name.with_ctx(ctx))
    }
}

impl Dialect {
    /// Create a new unregistered dialect.
    pub fn new(name: DialectName) -> Dialect {
        Dialect {
            name,
            ops: vec![],
            types: vec![],
            attributes: vec![],
        }
    }

    /// Register this dialect if not already registered.
    pub fn register(self, ctx: &mut Context) {
        ctx.dialects.entry(self.name.clone()).or_insert(self);
    }

    /// Add an [Op](crate::op::Op) to this dialect.
    pub fn add_op(&mut self, op: OpId) {
        assert!(op.dialect == self.name);
        self.ops.push(op);
    }

    /// Add a [Type](crate::type::Type) to this dialect.
    pub fn add_type(&mut self, ty: TypeId) {
        assert!(ty.dialect == self.name);
        self.types.push(ty);
    }

    /// Add an [Attribute](crate::attribute::Attribute) to this dialect.
    pub fn add_attr(&mut self, attr: AttrId) {
        assert!(attr.dialect == self.name);
        self.attributes.push(attr);
    }

    /// This Dialect's name.
    pub fn get_name(&self) -> &DialectName {
        &self.name
    }

    /// Get reference to a registered Dialect by name.
    pub fn get_ref(ctx: &Context, name: DialectName) -> Option<&Dialect> {
        ctx.dialects.get(&name)
    }

    /// Get mutable reference to a registered Dialect by name.
    pub fn get_mut(ctx: &mut Context, name: DialectName) -> Option<&mut Dialect> {
        ctx.dialects.get_mut(&name)
    }
}
