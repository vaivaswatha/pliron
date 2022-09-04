use std::ops::Deref;

use crate::{context::Context, op::OpId};

/// Dialect name: Safe wrapper around a String.
#[derive(Clone, Hash, PartialEq, Eq)]
pub struct DialectName(String);

impl DialectName {
    pub fn new(name: &str) -> DialectName {
        DialectName(name.to_string())
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
}

impl Dialect {
    /// Create a new unregistered dialect.
    pub fn new(name: DialectName) -> Dialect {
        Dialect { name, ops: vec![] }
    }

    /// Register this dialect if not already registered.
    pub fn register(self, ctx: &mut Context) {
        ctx.dialects.entry(self.name.clone()).or_insert(self);
    }

    /// Add an Op to this dialect.
    pub fn add_op(&mut self, op: OpId) {
        assert!(op.dialect == self.name);
        self.ops.push(op);
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
