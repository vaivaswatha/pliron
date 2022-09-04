use std::ops::Deref;

use downcast_rs::{impl_downcast, Downcast};

use crate::{
    common_traits::{Stringable, Verify},
    context::{Context, Ptr},
    dialect::{Dialect, DialectName},
    operation::Operation,
};

#[derive(Clone, Hash, PartialEq, Eq)]
/// An Op's name (not including it's dialect).
pub struct OpName(String);

impl OpName {
    pub fn new(name: &str) -> OpName {
        OpName(name.to_string())
    }
}

impl Deref for OpName {
    type Target = String;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// A combination of an Op's name and its dialect.
#[derive(Clone, Hash, PartialEq, Eq)]
pub struct OpId {
    pub dialect: DialectName,
    pub name: OpName,
}

pub(crate) type OpCreator = fn(Ptr<Operation>) -> OpObj;

/// A wrapper around Operation for Op(code) specific work.
/// All per-instance data must be in the underyling Operation.
pub trait Op: Downcast + Verify + Stringable {
    /// Get the underlying IR Operation
    fn get_operation(&self) -> Ptr<Operation>;
    /// Create a new Op object, given the containing operation.
    fn create(op: Ptr<Operation>) -> OpObj
    where
        Self: Sized;
    /// Get this Op's OpId
    fn get_opid(&self) -> OpId;
    /// Get this Op's OpId, without self reference.
    fn get_opid_static() -> OpId
    where
        Self: Sized;

    /// Register Op in Context and add it to dialect.
    fn register(ctx: &mut Context, dialect: &mut Dialect)
    where
        Self: Sized,
    {
        match ctx.ops.entry(Self::get_opid_static()) {
            std::collections::hash_map::Entry::Occupied(_) => (),
            std::collections::hash_map::Entry::Vacant(v) => {
                v.insert(Self::create);
                dialect.add_op(Self::get_opid_static());
            }
        }
    }
}
impl_downcast!(Op);

type OpObj = Box<dyn Op>;
