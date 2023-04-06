//! An [Op] is a thin wrapper arround an [Operation], providing
//! API specific to the [OpId] of that Operation.
//!
//! See MLIR's [Op](https://mlir.llvm.org/docs/Tutorials/Toy/Ch-2/#op-vs-operation-using-mlir-operations).
//!
//! Common semantics, API and behaviour of [Op]s are
//! abstracted into Op interfaces. Interfaces in pliron capture MLIR
//! functionality of both [Traits](https://mlir.llvm.org/docs/Traits/)
//! and [Interfaces](https://mlir.llvm.org/docs/Interfaces/).
//!
//! [Op]s that implement an interface can choose to annotate
//! the `impl` with [`#[cast_to]`](https://docs.rs/intertrait/latest/intertrait/#usage).
//! This will enable an [Op] reference to be [cast](op_cast)
//! into an interface object reference (or check if it [impls](op_impls) it).
//! Without this, the cast will always fail.
//!
//! [OpObj]s can be downcasted to their concrete types using
//! [downcast_rs](https://docs.rs/downcast-rs/1.2.0/downcast_rs/index.html#example-without-generics).

use std::ops::Deref;

use downcast_rs::{impl_downcast, Downcast};
use intertrait::{cast::CastRef, CastFrom};

use crate::{
    common_traits::{DisplayWithContext, Verify},
    context::{Context, Ptr},
    dialect::{Dialect, DialectName},
    operation::Operation,
    with_context::AttachContext,
};

#[derive(Clone, Hash, PartialEq, Eq)]
/// An Op's name (not including it's dialect).
pub struct OpName(String);

impl OpName {
    /// Create a new OpName.
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

impl AttachContext for OpName {}
impl DisplayWithContext for OpName {
    fn fmt(&self, _ctx: &Context, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// A combination of an [Op]'s name and its dialect.
#[derive(Clone, Hash, PartialEq, Eq)]
pub struct OpId {
    pub dialect: DialectName,
    pub name: OpName,
}

impl AttachContext for OpId {}
impl DisplayWithContext for OpId {
    fn fmt(&self, ctx: &Context, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "{}.{}",
            self.dialect.with_ctx(ctx),
            self.name.with_ctx(ctx)
        )
    }
}

pub(crate) type OpCreator = fn(Ptr<Operation>) -> OpObj;

/// A wrapper around [Operation] for Op(code) specific work.
/// All per-instance data must be in the underyling Operation.
///
/// See [module](crate::op) documentation for more information.
pub trait Op: Downcast + Verify + DisplayWithContext + CastFrom {
    /// Get the underlying IR Operation
    fn get_operation(&self) -> Ptr<Operation>;
    /// Create a new Op object, by wrapping around an operation.
    fn wrap_operation(op: Ptr<Operation>) -> OpObj
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
                v.insert(Self::wrap_operation);
                dialect.add_op(Self::get_opid_static());
            }
        }
    }
}
impl_downcast!(Op);

pub fn from_operation(ctx: &Context, op: Ptr<Operation>) -> OpObj {
    let opid = op.deref(ctx).get_opid();
    (ctx.ops
        .get(&opid)
        .unwrap_or_else(|| panic!("Unregistered Op {}", opid.with_ctx(ctx))))(op)
}

pub type OpObj = Box<dyn Op>;

/// Cast reference to an [Op] object to an interface reference.
pub fn op_cast<T: ?Sized + Op>(attr: &dyn Op) -> Option<&T> {
    attr.cast::<T>()
}

/// Does this [Op] object implement interface T?
pub fn op_impls<T: ?Sized + Op>(attr: &dyn Op) -> bool {
    attr.impls::<T>()
}

/// Declare an [Op] and fill boilerplate impl code.
///
/// Usage:
/// ```
/// declare_op!(
///     /// MyOp is mine
///     MyOp,
///     "name",
///     "dialect"
/// );
/// # use pliron::{
/// #     declare_op, with_context::AttachContext, common_traits::DisplayWithContext,
/// #     context::Context, error::CompilerError, common_traits::Verify
/// # };
/// # impl AttachContext for MyOp {}
/// # impl DisplayWithContext for MyOp {
/// #    fn fmt(&self, _ctx: &Context, _f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
/// #        todo!()
/// #    }
/// # }
///
/// # impl Verify for MyOp {
/// #   fn verify(&self, _ctx: &Context) -> Result<(), CompilerError> {
/// #        todo!()
/// #    }
/// # }
/// ```
///
/// This will generate the following code.
/// ```ignore
///     struct MyOp {
///       op: Ptr<Operation>,
///     }
///     impl Op for MyOp {...}
/// ```
/// **Note**: pre-requisite traits for [Op] must already be implemented.
#[macro_export]
macro_rules! declare_op {
    (   $(#[$outer:meta])*
        $structname: ident, $op_name: literal, $dialect_name: literal) => {
        #[derive(Clone, Copy)]
        $(#[$outer])*
        pub struct $structname { op: $crate::context::Ptr<$crate::operation::Operation> }
        impl $crate::op::Op for $structname {
            fn get_operation(&self) -> $crate::context::Ptr<$crate::operation::Operation> {
                self.op
            }

            fn wrap_operation(op: $crate::context::Ptr<$crate::operation::Operation>) -> $crate::op::OpObj {
                Box::new($structname { op })
            }

            fn get_opid(&self) -> $crate::op::OpId {
                Self::get_opid_static()
            }

            fn get_opid_static() -> $crate::op::OpId {
                $crate::op::OpId {
                    name: $crate::op::OpName::new($op_name),
                    dialect: $crate::dialect::DialectName::new($dialect_name),
                }
            }
        }
    }
}
