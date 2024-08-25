mod irfmt;
mod macro_attr;

mod derive_attr;
mod derive_op;
mod derive_printable;
mod derive_shared;
mod derive_type;
mod interfaces;

use proc_macro::TokenStream;

/// `#[def_attribute(...)]`: Annotate a Rust struct as a new IR attribute.
///
/// The argument to the macro is the fully qualified name of the attribute in the form of
/// `"dialect.attribute_name"`.
///
/// The macro will leave the struct definition unchanged, but it will generate an implementation of
/// the pliron::Attribute trait and implements other internal traits and types resources required
/// to use the IR attribute.
///
/// **Note**: pre-requisite traits for `Attribute` must already be implemented.
///         Additionaly, PartialEq must be implemented by the type.
///
/// Usage:
///
/// ```
/// use pliron_derive::def_attribute;
///
/// #[def_attribute("my_dialect.attribute")]
/// #[derive(Debug, Clone, PartialEq, Eq)]
/// pub struct StringAttr(String);
/// # use pliron::{impl_verify_succ, printable::{State, Printable}, context::Context};
/// # impl_verify_succ!(StringAttr);
/// # impl Printable for StringAttr {
/// #     fn fmt(&self, _ctx: &Context, _state: &State, f: &mut std::fmt::Formatter<'_>)
/// #      -> std::fmt::Result  { todo!() }
/// # }
/// ```
#[proc_macro_attribute]
pub fn def_attribute(args: TokenStream, input: TokenStream) -> TokenStream {
    to_token_stream(derive_attr::def_attribute(args, input))
}

/// `#[def_type(...)]`: Annotate a Rust struct as a new IR type.
///
/// The argument to the macro is the fully qualified name of the type in the form of
/// `"dialect.type_name"`.
///
/// The macro will leave the struct definition unchanged, but it will generate an implementation of
/// the pliron::Type trait and implements other internal traits and types resources required
/// to use the IR type.
///
/// **Note**: pre-requisite traits for `Type` must already be implemented.
///         Additionaly, [Hash](core::hash::Hash) and [Eq] must be implemented by the rust type.
///
/// Usage:
///
/// ```
/// use pliron_derive::def_type;
/// #[def_type("my_dialect.unit")]
/// #[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// pub struct UnitType;
/// # use pliron::{impl_verify_succ, printable::{State, Printable}, context::Context};
/// # impl_verify_succ!(UnitType);
/// # impl Printable for UnitType {
/// #     fn fmt(&self, _ctx: &Context, _state: &State, f: &mut std::fmt::Formatter<'_>)
/// #      -> std::fmt::Result  { todo!() }
/// # }
/// ```
#[proc_macro_attribute]
pub fn def_type(args: TokenStream, input: TokenStream) -> TokenStream {
    to_token_stream(derive_type::def_type(args, input))
}

/// `#[def_op(...)]`: Create a new IR operation.
///
/// The argument to the macro is the fully qualified name of the operation in the form of
/// `"dialect.op_name"`.
///
/// The macro assumes an empty struct and will add the `op: Ptr<Operation>` field used to access
/// the underlying Operation in the context.
///
/// The macro will automatically derive the `Clone`, `Copy`, `Hash`, `PartialEq` and `Eq` traits
/// for the new struct definition.
///
/// **Note**: pre-requisite traits for `Op` (Printable, Verify etc) must already be implemented
///
/// Usage:
///
/// ```
/// use pliron_derive::def_op;
/// use pliron::{impl_canonical_syntax, impl_verify_succ};
///
/// #[def_op("my_dialect.op")]
/// pub struct MyOp;
/// impl_canonical_syntax!(MyOp);
/// impl_verify_succ!(MyOp);
/// ```
/// The example will create a struct definition equivalent to:
///
/// ```
/// #[derive(Clone, Copy, PartialEq, Eq, Hash)]
/// pub struct MyOp {
///   op: Ptr<Operation>,
/// }
/// # use pliron::{context::Ptr, operation::Operation};
/// ```
#[proc_macro_attribute]
pub fn def_op(args: TokenStream, input: TokenStream) -> TokenStream {
    to_token_stream(derive_op::def_op(args, input))
}

/// The derive macro is normally used together with one of the `#[def_attribute]`, `#[def_type]` or
/// `#[def_op]` proc macros.
///
/// An optional format string can be provided to the derive macro using the `ir_format` attribute.
/// The `ir_kind` macro attribute is normally filled in by the `def_x` proc macros.
#[proc_macro_derive(Printable, attributes(ir_kind, ir_format))]
pub fn derive_printable(input: TokenStream) -> TokenStream {
    to_token_stream(derive_printable::derive(input))
}

pub(crate) fn to_token_stream(res: syn::Result<proc_macro2::TokenStream>) -> TokenStream {
    let tokens = match res {
        Ok(tokens) => tokens,
        Err(error) => {
            let error = error.to_compile_error();
            quote::quote!(
                #error
            )
        }
    };
    TokenStream::from(tokens)
}

// Helper derive macro to accept internal attributes that we pass to Printable,
// Parsable and other derive macros. The helper ensures that the injected attributes
// do not cause a compilation error if no other derive macro is used.
#[doc(hidden)]
#[proc_macro_derive(DeriveAttribAcceptor, attributes(ir_kind))]
pub fn derive_attrib_dummy(_input: TokenStream) -> TokenStream {
    TokenStream::new()
}

/// Declare an [Op](../pliron/op/trait.Op.html) interface, which can be implemented
/// by any `Op`.
///
/// If the interface requires any other interface to be already implemented,
/// they can be specified super-traits.
///
/// When an `Op` is verified, its interfaces are also automatically verified,
/// with guarantee that a super-interface is verified before an interface itself is.
///
/// Example: Here `SameOperandsAndResultType` and `SymbolOpInterface` are super interfaces
/// for the new interface `MyOpIntr`.
/// ```
/// # use pliron::builtin::op_interfaces::{SameOperandsAndResultType, SymbolOpInterface};
/// # use pliron_derive::{op_interface};
/// # use pliron::{op::Op, context::Context, result::Result};
///   /// MyOpIntr is my first op interface.
///   #[op_interface]
///   trait MyOpIntr: SameOperandsAndResultType + SymbolOpInterface {
///       fn verify(_op: &dyn Op, _ctx: &Context) -> Result<()>
///       where Self: Sized,
///       {
///           Ok(())
///       }
///   }
/// ```
#[proc_macro_attribute]
pub fn op_interface(_attr: TokenStream, item: TokenStream) -> TokenStream {
    to_token_stream(interfaces::op_interface_define(item))
}

/// Implement [Op](../pliron/op/trait.Op.html) Interface for an Op. The interface trait must define
/// a `verify` function with type [OpInterfaceVerifier](../pliron/op/type.OpInterfaceVerifier.html)
///
/// Usage:
/// ```
/// # use pliron_derive::{def_op, op_interface, op_interface_impl};
///
/// #[def_op("dialect.name")]
/// struct MyOp;
///
/// #[op_interface]
/// pub trait MyOpInterface {
///     fn gubbi(&self);
///     fn verify(op: &dyn Op, ctx: &Context) -> Result<()>
///     where Self: Sized,
///     {
///         Ok(())
///     }
/// }
///
/// #[op_interface_impl]
/// impl MyOpInterface for MyOp {
///     fn gubbi(&self) { println!("gubbi"); }
/// }
/// # use pliron::{
/// #     op::Op, context::Context, result::Result, common_traits::Verify
/// # };
/// # pliron::impl_verify_succ!(MyOp);
/// # pliron::impl_canonical_syntax!(MyOp);
/// ```
#[proc_macro_attribute]
pub fn op_interface_impl(_attr: TokenStream, item: TokenStream) -> TokenStream {
    to_token_stream(interfaces::op_interface_impl(item))
}

/// Derive implementation of an [Op](../pliron/op/trait.Op.html) Interface for an Op.
/// Note that an impl can be derived only for those interfaces that do not require any
/// methods to be defined during the impl.
///
/// Usage:
/// ```
/// # use pliron_derive::{op_interface, derive_op_interface_impl};
///
/// #[def_op("dialect.name")]
/// #[derive_op_interface_impl(MyOpInterface)]
/// struct MyOp;
///
/// #[op_interface]
/// pub trait MyOpInterface {
///     fn gubbi(&self) { println!("gubbi"); }
///     fn verify(op: &dyn Op, ctx: &Context) -> Result<()>
///     where Self: Sized,
///     {
///         Ok(())
///     }
/// }
/// # use pliron_derive::def_op;
/// # use pliron::{
/// #     op::Op, context::Context, result::Result,
/// #     common_traits::Verify
/// # };
/// # pliron::impl_verify_succ!(MyOp);
/// # pliron::impl_canonical_syntax!(MyOp);
/// ```
#[proc_macro_attribute]
pub fn derive_op_interface_impl(attr: TokenStream, item: TokenStream) -> TokenStream {
    to_token_stream(interfaces::derive_op_interface_impl(attr, item))
}
