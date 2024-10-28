mod derive_attr;
mod derive_format;
mod derive_op;
mod derive_type;
mod interfaces;
mod irfmt;

use proc_macro::TokenStream;
use quote::format_ident;
use syn::parse_quote;

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
/// use pliron::derive::def_attribute;
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
/// use pliron::derive::def_type;
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
/// use pliron::derive::def_op;
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

/// Derive [Format](../pliron/irfmt/trait.Format.html) for [Op](../pliron/op/trait.Op.html)s
/// This derive only supports a syntax in which results appear before the opid:
///   res1, ... = opid ...
/// The format string only specifies what comes after the opid.
///   1. A named variable $name specifies a named attribute of the operation.
///   2. An unnamed variable $i specifies the `operands[i]`.
#[proc_macro_attribute]
pub fn op_format(args: TokenStream, input: TokenStream) -> TokenStream {
    to_token_stream(derive_format::op_derive(args, input))
}

/// Derive [Format](../pliron/irfmt/trait.Format.html) for Rust types other than Ops.
///   1. A named variable $name specifies a named struct field.
///   2. An unnamed variable $i specifies the i'th field of a tuple struct.
#[proc_macro_attribute]
pub fn format(args: TokenStream, input: TokenStream) -> TokenStream {
    to_token_stream(derive_format::derive(args, input))
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
/// # use pliron::derive::{op_interface};
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
    let supertrait = parse_quote! { ::pliron::op::Op };
    let interface_deps_slice = parse_quote! { ::pliron::op::OP_INTERFACE_DEPS };

    to_token_stream(interfaces::interface_define(
        item,
        supertrait,
        interface_deps_slice,
    ))
}

/// Implement [Op](../pliron/op/trait.Op.html) Interface for an Op. The interface trait must define
/// a `verify` function with type [OpInterfaceVerifier](../pliron/op/type.OpInterfaceVerifier.html)
///
/// Usage:
/// ```
/// # use pliron::derive::{def_op, op_interface, op_interface_impl};
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
    let interface_verifiers_slice = parse_quote! { ::pliron::op::OP_INTERFACE_VERIFIERS };
    let id = parse_quote! { ::pliron::op::OpId };
    let get_id_static = format_ident!("{}", "get_opid_static");
    let verifier_type = parse_quote! { ::pliron::op::OpInterfaceVerifier };
    to_token_stream(interfaces::interface_impl(
        item,
        interface_verifiers_slice,
        id,
        verifier_type,
        get_id_static,
    ))
}

/// Derive implementation of an [Op](../pliron/op/trait.Op.html) Interface for an Op.
/// Note that an impl can be derived only for those interfaces that do not require any
/// methods to be defined during the impl.
///
/// Usage:
/// ```
/// # use pliron::derive::{op_interface, derive_op_interface_impl};
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
/// # use pliron::derive::def_op;
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

/// Declare an [Attribute](../pliron/attribute/trait.Attribute.html) interface,
/// which can be implemented by any `Attribute`.
///
/// If the interface requires any other interface to be already implemented,
/// they can be specified super-traits.
///
/// When an `Attribute` is verified, its interfaces are also automatically verified,
/// with guarantee that a super-interface is verified before an interface itself is.
///
/// Example: Here `Super1` and `Super2` are super interfaces for the interface `MyAttrIntr`.
/// ```
/// # use pliron::{attribute::Attribute, context::Context, result::Result};
/// use pliron::derive::attr_interface;
///
/// #[attr_interface]
/// trait Super1 {
///     fn verify(_attr: &dyn Attribute, _ctx: &Context) -> Result<()>
///     where
///         Self: Sized,
///     {
///         Ok(())
///     }
/// }
///
/// #[attr_interface]
/// trait Super2 {
///     fn verify(_attr: &dyn Attribute, _ctx: &Context) -> Result<()>
///     where
///         Self: Sized,
///     {
///         Ok(())
///     }
/// }
///
/// // MyAttrIntr is my best attribute interface.
/// #[attr_interface]
/// trait MyAttrIntr: Super1 + Super2 {
///     fn verify(_attr: &dyn Attribute, _ctx: &Context) -> Result<()>
///     where
///         Self: Sized,
///     {
///         Ok(())
///     }
/// }
/// ```
#[proc_macro_attribute]
pub fn attr_interface(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let supertrait = parse_quote! { ::pliron::attribute::Attribute };
    let interface_deps_slice = parse_quote! { ::pliron::attribute::ATTR_INTERFACE_DEPS };

    to_token_stream(interfaces::interface_define(
        item,
        supertrait,
        interface_deps_slice,
    ))
}

/// Implement [Attribute](../pliron/attribute/trait.Attribute.html) Interface for an Attribute.
/// The interface trait must define a `verify` function with type
/// [AttrInterfaceVerifier](../pliron/attribute/type.AttrInterfaceVerifier.html).
///
/// Usage:
/// ```
/// use pliron::derive::{attr_interface, attr_interface_impl};
///
/// #[def_attribute("dialect.name")]
/// #[derive(PartialEq, Eq, Clone, Debug)]
/// struct MyAttr { }
///
///     /// My first attribute interface.
/// #[attr_interface]
/// trait MyAttrInterface {
///     fn monu(&self);
///     fn verify(attr: &dyn Attribute, ctx: &Context) -> Result<()>
///     where Self: Sized,
///     {
///          Ok(())
///     }
/// }
///
/// #[attr_interface_impl]
/// impl MyAttrInterface for MyAttr
/// {
///     fn monu(&self) { println!("monu"); }
/// }
/// # use pliron::{
/// #     printable::{self, Printable},
/// #     context::Context, result::Result, common_traits::Verify,
/// #     attribute::Attribute
/// # };
/// # use pliron::derive::def_attribute;
/// #
/// # impl Printable for MyAttr {
/// #    fn fmt(&self, _ctx: &Context, _state: &printable::State, _f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
/// #        unimplemented!()
/// #    }
/// # }
/// # pliron::impl_verify_succ!(MyAttr);
#[proc_macro_attribute]
pub fn attr_interface_impl(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let interface_verifiers_slice = parse_quote! { ::pliron::attribute::ATTR_INTERFACE_VERIFIERS };
    let id = parse_quote! { ::pliron::attribute::AttrId };
    let get_id_static = format_ident!("{}", "get_attr_id_static");
    let verifier_type = parse_quote! { ::pliron::attribute::AttrInterfaceVerifier };
    to_token_stream(interfaces::interface_impl(
        item,
        interface_verifiers_slice,
        id,
        verifier_type,
        get_id_static,
    ))
}

/// Declare a [Type](../pliron/type/trait.Type.html) interface,
/// which can be implemented by any `Type`.
///
/// If the interface requires any other interface to be already implemented,
/// they can be specified super-traits.
///
/// When an `Attribute` is verified, its interfaces are also automatically verified,
/// with guarantee that a super-interface is verified before an interface itself is.
///
/// Example: Here `Super1` and `Super2` are super interfaces for the interface `MyTypeIntr`.
/// ```
/// use pliron::derive::type_interface;
/// # use pliron::{r#type::Type, context::Context, result::Result};
/// #[type_interface]
/// trait Super1 {
///     fn verify(_type: &dyn Type, _ctx: &Context) -> Result<()>
///     where
///         Self: Sized,
///     {
///         Ok(())
///     }
/// }
///
/// #[type_interface]
/// trait Super2 {
///     fn verify(_type: &dyn Type, _ctx: &Context) -> Result<()>
///     where
///         Self: Sized,
///     {
///         Ok(())
///     }
/// }
///
/// #[type_interface]
/// // MyTypeIntr is my best type interface.
/// trait MyTypeIntr: Super1 + Super2 {
///     fn verify(_type: &dyn Type, _ctx: &Context) -> Result<()>
///     where
///         Self: Sized,
///     {
///         Ok(())
///     }
/// }
/// ```
#[proc_macro_attribute]
pub fn type_interface(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let supertrait = parse_quote! { ::pliron::r#type::Type };
    let interface_deps_slice = parse_quote! { ::pliron::r#type::TYPE_INTERFACE_DEPS };

    to_token_stream(interfaces::interface_define(
        item,
        supertrait,
        interface_deps_slice,
    ))
}

/// Implement [Type](../pliron/type/trait.Type.html) Interface for a Type.
/// The interface trait must define a `verify` function with type
/// [TypeInterfaceVerifier](../pliron/type/type.TypeInterfaceVerifier.html).
///
/// Usage:
/// ```
/// use pliron::derive::{type_interface, type_interface_impl};
///
/// #[def_type("dialect.name")]
/// #[derive(PartialEq, Eq, Clone, Debug, Hash)]
/// struct MyType { }
///
/// #[type_interface]
/// /// My first type interface.
/// trait MyTypeInterface {
///     fn monu(&self);
///     fn verify(r#type: &dyn Type, ctx: &Context) -> Result<()>
///     where Self: Sized,
///     {
///          Ok(())
///     }
/// }
///
/// #[type_interface_impl]
/// impl MyTypeInterface for MyType
/// {
///     fn monu(&self) { println!("monu"); }
/// }
/// # use pliron::{
/// #     printable::{self, Printable},
/// #     context::Context, result::Result, common_traits::Verify,
/// #     r#type::Type
/// # };
/// # use pliron::derive::def_type;
/// #
/// # impl Printable for MyType {
/// #    fn fmt(&self, _ctx: &Context, _state: &printable::State, _f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
/// #        unimplemented!()
/// #    }
/// # }
/// # pliron::impl_verify_succ!(MyType);
#[proc_macro_attribute]
pub fn type_interface_impl(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let interface_verifiers_slice = parse_quote! { ::pliron::r#type::TYPE_INTERFACE_VERIFIERS };
    let id = parse_quote! { ::pliron::r#type::TypeId };
    let get_id_static = format_ident!("{}", "get_type_id_static");
    let verifier_type = parse_quote! { ::pliron::r#type::TypeInterfaceVerifier };
    to_token_stream(interfaces::interface_impl(
        item,
        interface_verifiers_slice,
        id,
        verifier_type,
        get_id_static,
    ))
}
