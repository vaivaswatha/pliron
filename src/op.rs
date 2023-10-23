//! An [Op] is a thin wrapper arround an [Operation], providing
//! API specific to the [OpId] of that Operation.
//!
//! See MLIR's [Op](https://mlir.llvm.org/docs/Tutorials/Toy/Ch-2/#op-vs-operation-using-mlir-operations).
//!
//! New [Op]s can be easily declared using the [declare_op](crate::declare_op) macro.
//!
//! Common semantics, API and behaviour of [Op]s are
//! abstracted into Op interfaces. Interfaces in pliron capture MLIR
//! functionality of both [Traits](https://mlir.llvm.org/docs/Traits/)
//! and [Interfaces](https://mlir.llvm.org/docs/Interfaces/).
//! Interfaces must all implement an associated function named `verify` with
//! the type [OpInterfaceVerifier].
//!
//! [Op]s that implement an interface must do so using the
//! [impl_op_interface](crate::impl_op_interface) macro.
//! This ensures that the interface verifier is automatically called,
//! and that a `&dyn Op` object can be [cast](op_cast) into an interface object,
//! (or that it can be checked if the interface is [implemented](op_impls))
//! with ease.
//!
//! [OpObj]s can be downcasted to their concrete types using
//! [downcast_rs](https://docs.rs/downcast-rs/1.2.0/downcast_rs/index.html#example-without-generics).

use std::{fmt::Display, ops::Deref};

use downcast_rs::{impl_downcast, Downcast};
use intertrait::{cast::CastRef, CastFrom};

use crate::{
    common_traits::Verify,
    context::{Context, Ptr},
    dialect::{Dialect, DialectName},
    error::Result,
    operation::Operation,
    parsable::ParserFn,
    printable::{self, Printable},
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

impl Printable for OpName {
    fn fmt(
        &self,
        _ctx: &Context,
        _state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        <Self as Display>::fmt(self, f)
    }
}

impl Display for OpName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// A combination of an [Op]'s name and its dialect.
#[derive(Clone, Hash, PartialEq, Eq)]
pub struct OpId {
    pub dialect: DialectName,
    pub name: OpName,
}

impl Printable for OpId {
    fn fmt(
        &self,
        _ctx: &Context,
        _state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        <Self as Display>::fmt(self, f)
    }
}

impl Display for OpId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.{}", self.dialect, self.name)
    }
}

pub(crate) type OpCreator = fn(Ptr<Operation>) -> OpObj;

/// A wrapper around [Operation] for Op(code) specific work.
/// All per-instance data must be in the underyling Operation,
/// which means that [OpObj]s are light-weight.
///
/// See [module](crate::op) documentation for more information.
pub trait Op: Downcast + Verify + Printable + CastFrom {
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

    /// Verify all interfaces implemented by this op.
    fn verify_interfaces(&self, ctx: &Context) -> Result<()>;

    /// Register Op in Context and add it to dialect.
    fn register(ctx: &mut Context, dialect: &mut Dialect, op_parser: ParserFn<OpObj>)
    where
        Self: Sized,
    {
        match ctx.ops.entry(Self::get_opid_static()) {
            std::collections::hash_map::Entry::Occupied(_) => (),
            std::collections::hash_map::Entry::Vacant(v) => {
                v.insert(Self::wrap_operation);
                dialect.add_op(Self::get_opid_static(), op_parser);
            }
        }
    }
}
impl_downcast!(Op);

/// Create [OpObj] from [`Ptr<Operation>`](Operation)
pub(crate) fn from_operation(ctx: &Context, op: Ptr<Operation>) -> OpObj {
    let opid = op.deref(ctx).get_opid();
    (ctx.ops
        .get(&opid)
        .unwrap_or_else(|| panic!("Unregistered Op {}", opid.disp(ctx))))(op)
}

/// [Op] objects are boxed and stored in the IR.
pub type OpObj = Box<dyn Op>;

/// Cast reference to an [Op] object to an interface reference.
pub fn op_cast<T: ?Sized + Op>(op: &dyn Op) -> Option<&T> {
    op.cast::<T>()
}

/// Does this [Op] object implement interface T?
pub fn op_impls<T: ?Sized + Op>(op: &dyn Op) -> bool {
    op.impls::<T>()
}

/// Every op interface must have a function named `verify` with this type.
pub type OpInterfaceVerifier = fn(&dyn Op, &Context) -> Result<()>;

/// Declare an [Op]
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
/// #     op::Op, declare_op, printable::{self, Printable},
/// #     context::Context, error::Result, common_traits::Verify
/// # };
/// # impl Printable for MyOp {
/// #    fn fmt(&self, _ctx: &Context, _state: &printable::State, _f: &mut core::fmt::Formatter<'_>)
/// #     -> core::fmt::Result
/// #    {
/// #        todo!()
/// #    }
/// # }
///
/// # impl Verify for MyOp {
/// #   fn verify(&self, _ctx: &Context) -> Result<()> {
/// #        todo!()
/// #    }
/// # }
/// ```
/// **Note**: pre-requisite traits for [Op] must already be implemented.
#[macro_export]
macro_rules! declare_op {
    (   $(#[$outer:meta])*
        $structname: ident, $op_name: literal, $dialect_name: literal) => {
        paste::paste!{
            /// Interface verifier
            #[allow(non_camel_case_types)]
            pub struct [<OpInterfaceVerifier_ $structname>](pub $crate::op::OpInterfaceVerifier);
            impl $structname {
                /// Returns the interface verifier
                pub const fn build_interface_verifier(verifier: $crate::op::OpInterfaceVerifier) ->
                [<OpInterfaceVerifier_ $structname>] {
                    [<OpInterfaceVerifier_ $structname>](verifier)
                }
            }
            inventory::collect!([<OpInterfaceVerifier_ $structname>]);
        }
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

            fn verify_interfaces(&self, ctx: &Context) -> $crate::error::Result<()> {
                let interface_verifiers = paste::paste!{
                    inventory::iter::<[<OpInterfaceVerifier_ $structname>]>
                };
                for verifier in interface_verifiers {
                    (verifier.0)(self, ctx)?;
                }
                Ok(())
            }
        }
    }
}

/// Implement an Op Interface for an Op. The interface trait must define
/// a `verify` function with type [OpInterfaceVerifier]
///
/// Usage:
/// ```
/// declare_op!(
///     /// MyOp is mine
///     MyOp,
///     "name",
///     "dialect"
/// );
/// trait MyOpInterface: Op {
///     fn gubbi(&self);
///     fn verify(op: &dyn Op, ctx: &Context) -> Result<()>
///         where
///         Self: Sized,
///     {
///         Ok(())
///     }
/// }
/// impl_op_interface!(
///     MyOpInterface for MyOp
///     {
///         fn gubbi(&self) { println!("gubbi"); }
///     }
/// );
/// # use pliron::{
/// #     op::Op, declare_op, impl_op_interface,
/// #     printable::{self, Printable}, context::Context, error::Result,
/// #     common_traits::Verify
/// # };
/// # impl Printable for MyOp {
/// #    fn fmt(&self, _ctx: &Context, _state: &printable::State, _f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
/// #        todo!()
/// #    }
/// # }
///
/// # impl Verify for MyOp {
/// #   fn verify(&self, _ctx: &Context) -> Result<()> {
/// #        todo!()
/// #    }
/// # }
#[macro_export]
macro_rules! impl_op_interface {
    ($intr_name:ident for $op_name:path { $($tt:tt)* }) => {
        paste::paste!{
            inventory::submit! {
                $op_name::build_interface_verifier(<$op_name as $intr_name>::verify)
            }
        }

        #[intertrait::cast_to]
        impl $intr_name for $op_name {
            $($tt)*
        }
    };
}
