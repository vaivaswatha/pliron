mod derive_attr;
mod derive_format;
mod derive_op;
mod derive_type;
mod interfaces;
mod irfmt;

use proc_macro::TokenStream;
use quote::format_ident;
use syn::parse_quote;

use derive_format::DeriveIRObject;

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
///         Additionaly, [Eq] and [Hash](core::hash::Hash) must be implemented by the type.
///
/// Usage:
///
/// ```
/// use pliron::derive::def_attribute;
///
/// #[def_attribute("my_dialect.attribute")]
/// #[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

/// Derive getter and setters for operation attributes listed as arguments.
/// The arguments are a comma separated list of attribute names
/// (which must be an [Identifier](../pliron/identifier/struct.Identifier.html)),
/// each of which may have an optional concrete Rust type specified,
/// denoting the [Attribute](../pliron/attribute/trait.Attribute.html)'s concrete type.
/// ```
/// # use pliron::derive::{def_op, derive_attr_get_set};
/// # use pliron::{impl_canonical_syntax, impl_verify_succ};
/// // A test for the `derive_attr_get_set` macro.
/// #[def_op("llvm.with_attrs")]
/// #[derive_attr_get_set(name_any_attr, name_ty_attr : pliron::builtin::attributes::TypeAttr)]
/// pub struct WithAttrsOp {}
/// # impl_canonical_syntax!(WithAttrsOp);
/// # impl_verify_succ!(WithAttrsOp);
/// ```
#[proc_macro_attribute]
pub fn derive_attr_get_set(args: TokenStream, input: TokenStream) -> TokenStream {
    to_token_stream(derive_op::derive_attr_get_set(args, input))
}

/// Derive [Printable](../pliron/printable/trait.Printable.html) and
/// [Parsable](../pliron/parsable/trait.Parsable.html) for Rust types.
/// Use this is for types other than `Op`, `Type` and `Attribute`s.
///   1. A named variable `$name` specifies a named struct field.
///   2. An unnamed variable `$i` specifies the i'th field of a tuple struct.
///
/// Struct (or tuple) fields that are either [Option] or [Vec] must to be specified
/// using the `opt` and `vec` directives respectively. The `opt` directive takes one argument,
/// a variable specifying the field name with type `Option`. The `vec` directive takes two
/// arguments, the first is a variable specifying the field name with type `Vec` and the second
/// is another directive to specify a [ListSeparator](../pliron/printable/enum.ListSeparator.html).
/// The following directives are supported:
///   1. `NewLine`: takes no argument, and specifies a newline to be used as list separator.
///   2. ``CharNewline(`c`)``: takes a single character argument that will be followed by a newline.
///   3. ``Char(`c`)``: takes a single character argument that will be used as separator.
///   4. ``CharSpace(`c`)``: takes a single character argument that will be followed by a space.
///
/// Examples:
/// 1. Derive for a struct, with no format string (default format):
///    (Note that the field u64 has both `Printable` and `Parsable` implemented).
/// ```
/// use pliron::derive::format;
/// #[format]
/// struct IntWrapper {
///    inner: u64,
/// }
/// ```
/// 2. An example with a custom format string:
/// ```
/// use pliron::derive::format;
/// #[format("`BubbleWrap` `[` $inner `]`")]
/// struct IntWrapperCustom {
///   inner: u64,
/// }
/// ```
/// 3. An example for an enum (custom format strings are allowed for the variants only).
/// ```
/// use pliron::derive::format;
/// use pliron::{builtin::types::IntegerType, r#type::TypePtr};
/// #[format]
/// enum Enum {
///     A(TypePtr<IntegerType>),
///     B {
///         one: TypePtr<IntegerType>,
///         two: u64,
///     },
///     C,
///     #[format("`<` $upper `/` $lower `>`")]
///     Op {
///         upper: u64,
///         lower: u64,
///     },
/// }
/// ```
/// 4. An example with `Option` and `Vec` fields
/// ```
/// use pliron::derive::format;
/// #[format("`<` opt($a) `;` vec($b, Char(`,`)) `>`")]
/// struct OptAndVec {
///    a: Option<u64>,
///    b: Vec<u64>,
///}
/// ```
#[proc_macro_attribute]
pub fn format(args: TokenStream, input: TokenStream) -> TokenStream {
    to_token_stream(derive_format::derive(
        args,
        input,
        DeriveIRObject::AnyOtherRustType,
    ))
}

/// Derive [Printable](../pliron/printable/trait.Printable.html) and
/// [Parsable](../pliron/parsable/trait.Parsable.html) for [Op](../pliron/op/trait.Op.html)s
/// This derive only supports a syntax in which results appear before the opid:
///   `res1, ... = opid ...`
/// The format string specifies what comes after the opid.
///   1. A named variable `$name` specifies a named attribute of the operation.
///      This cannot be combined with the "attr_dict" directive.
///   2. An unnamed variable `$i` specifies `operands[i]`, except when inside some directives.
///      This cannot be combined with the "operands" directive.
///   3. The "type" directive specifies that a type must be parsed. It takes one argument,
///      which is an unnamed variable `$i` with `i` specifying `result[i]`.
///   4. The "region" directive specifies that a region must be parsed. It takes one argument,
///      which is an unnamed variable `$i` with `i` specifying `region[i]`. This cannot be
///      combined with the "regions" directive.
///   5. The "attr" directive can be used to specify attribute on an `Op` when the attribute's
///      rust type is fixed at compile time. It takes two arguments, the first is the attribute name
///      and the second is the concrete rust type of the attribute. This second argument can be a
///      named variable `$Name` (with `Name` being in scope) or a literal string denoting the path
///      to a rust type (e.g. `` `::pliron::builtin::attributes::IntegerAttr` ``).
///      The advantage over specifying the attribute as a named variable is that the attribute-id
///      is not a part of the syntax here, allowing it to be more succinct.
///      This cannot be combined with the "attr_dict" directive.
///   6. The "succ" directive specifies an operation's successor. It takes one argument,
///      which is an unnamed variable `$i` with `i` specifying `successor[i]`.
///   7. The "operands" directive specifies all the operands of an operation. It takes one argument
///      which is a directive specifying the separator between operands.
///      The following directives are supported:
///        1. `NewLine`: takes no argument, and specifies a newline to be used as list separator.
///        2. ``CharNewline(`c`)``: takes a single character argument that will be followed by a newline.
///        3. ``Char(`c`)``: takes a single character argument that will be used as separator.
///        4. ``CharSpace(`c`)``: takes a single character argument that will be followed by a space.
///   8. The "successors" directive specifies all the successors of an operation. It takes one argument
///      which is a directive specifying the separator between successors. The separator directive is same
///      as that for "operands" above. This cannot be combined with the "succ" directive.
///   9. The "regions" directive specifies all the regions of an operation. It takes one argument
///      which is a directive specifying the separator between regions. The separator directive is same
///      as that for "operands" above. This cannot be combined with the "region" directive.
///  10. The "attr_dict" directive specifies an [AttributeDict](../pliron/attribute/struct.AttributeDict.html).
///      It cannot be combined with either the "attr" directive or a named variable (`$name`).
///
/// Examples:
/// 1. Derive for a struct, with no format string (default format):
/// ```
/// use pliron::derive::{def_op, format_op};
/// use pliron::impl_verify_succ;
/// #[format_op]
/// #[def_op("test.myop")]
/// struct MyOp;
/// impl_verify_succ!(MyOp);
/// ```
/// 2. An example with a custom format string:
/// ```
/// use pliron::derive::{def_op, format_op, derive_op_interface_impl};
/// use pliron::impl_verify_succ;
/// use pliron::{op::Op, builtin::op_interfaces::{OneOpdInterface, OneResultInterface}};
/// #[format_op("$0 `<` $attr `>` `:` type($0)")]
/// #[def_op("test.one_result_one_operand")]
/// #[derive_op_interface_impl(OneOpdInterface, OneResultInterface)]
/// struct OneResultOneOperandOp;
/// impl_verify_succ!(OneResultOneOperandOp);
#[proc_macro_attribute]
pub fn format_op(args: TokenStream, input: TokenStream) -> TokenStream {
    to_token_stream(derive_format::derive(args, input, DeriveIRObject::Op))
}

/// Derive [Printable](../pliron/printable/trait.Printable.html) and
/// [Parsable](../pliron/parsable/trait.Parsable.html) for
/// [Attribute](../pliron/attribute/trait.Attribute.html)s
///
/// Refer to [macro@format] for the syntax specification and examples.
#[proc_macro_attribute]
pub fn format_attribute(args: TokenStream, input: TokenStream) -> TokenStream {
    to_token_stream(derive_format::derive(
        args,
        input,
        DeriveIRObject::Attribute,
    ))
}
/// Derive [Printable](../pliron/printable/trait.Printable.html) and
/// [Parsable](../pliron/parsable/trait.Parsable.html) for
/// [Type](../pliron/type/trait.Type.html)s
///
/// Refer to [macro@format] for the syntax specification and examples.
#[proc_macro_attribute]
pub fn format_type(args: TokenStream, input: TokenStream) -> TokenStream {
    to_token_stream(derive_format::derive(args, input, DeriveIRObject::Type))
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
        true,
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
        true,
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
/// #[derive(PartialEq, Eq, Clone, Debug, Hash)]
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
        false,
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
