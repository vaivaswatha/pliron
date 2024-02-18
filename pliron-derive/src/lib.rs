mod irfmt;
mod macro_attr;

mod derive_attr;
mod derive_op;
mod derive_printable;
mod derive_shared;
mod derive_type;

use proc_macro::TokenStream;

/// The `#[def_attribute(...)]` proc macro.
///
/// The macro can be used to annotate a Rust struct as a new IR attribute.
///
/// The argument to the macro is the fully qualified name of the attribute in the form of
/// `"dialect.attribute_name"`.
///
/// The macro will leave the struct definition unchanged, but it will generate an implementation of
/// the pliron::Attribute trait and implements other internal traits and types resources required
/// to use the IR attribute.
///
/// Usage:
///
/// ```ignore
/// #[def_attribute("my_dialect.attribute")]
/// #[derive(Debug, Clone, PartialEq, Eq)]
/// pub struct StringAttr(String);
/// ```
///
/// **Note**: pre-requisite traits for `Attribute` must already be implemented.
///         Additionaly, PartialEq must be implemented by the type.
#[proc_macro_attribute]
pub fn def_attribute(args: TokenStream, input: TokenStream) -> TokenStream {
    to_token_stream(derive_attr::def_attribute(args, input))
}

/// The `#[def_type(...)]` proc macro.
///
/// The macro can be used to annotate a Rust struct as a new IR type.
///
/// The argument to the macro is the fully qualified name of the type in the form of
/// `"dialect.type_name"`.
///
/// The macro will leave the struct definition unchanged, but it will generate an implementation of
/// the pliron::Type trait and implements other internal traits and types resources required
/// to use the IR type.
///
/// Usage:
///
/// ```ignore
/// #[def_type("my_dialect.unit")]
/// #[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// pub struct UnitType();
/// ```
///
/// **Note**: pre-requisite traits for `Type` must already be implemented.
///         Additionaly, Hash and Eq must be implemented by the rust type.
#[proc_macro_attribute]
pub fn def_type(args: TokenStream, input: TokenStream) -> TokenStream {
    to_token_stream(derive_type::def_type(args, input))
}

/// The `#[def_op(...)]` proc macro.
///
/// The `#[def_op("dialect.op"]` can be used to to create a new IR operation.
///
/// The argument to the macro is the fully qualified name of the operation in the form of
/// `"dialect.op_name"`.
///
/// The macro assumes an empty struct and will add the `op: Ptr<Operation>` field used to access
/// the underlying Operation in the context.
///
/// The macro will automatically derive the `Clone` and `Copy` traits for the new struct
/// definition.
///
/// Usage:
///
/// ```ignore
/// #[def_op("my_dialect.op")]
/// pub struct MyOp {}
/// ```
///
/// The example will create a struct definition equivalent to:
///
/// ```ignore
/// #[derive(Clone, Copy)]
/// pub struct MyOp {
///   op: Ptr<Operation>,
/// }
/// ```
#[proc_macro_attribute]
pub fn def_op(args: TokenStream, input: TokenStream) -> TokenStream {
    to_token_stream(derive_op::def_op(args, input))
}

#[proc_macro_derive(Printable, attributes(dialect, ir_kind, ir_format))]
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

// Helper derive macro to accept internal attributes that we pass to Printable, Parsable and other
// derive macros. The helper ensures that the injected attributes do not cause a compilation error if no other derive macro is used.
#[proc_macro_derive(DeriveAttribAcceptor, attributes(ir_kind))]
pub fn derive_attrib_dummy(_input: TokenStream) -> TokenStream {
    TokenStream::new()
}
