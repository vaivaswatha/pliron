mod attr;

mod derive_attr;
mod derive_op;
mod derive_shared;
mod derive_type;

use proc_macro::TokenStream;

/// The `#[def_attribute]` proc macro.
///
/// The macro can be used to annotate a Rust struct as a new IR attribute.
///
/// The macro will leave the struct definition unchanged, but it will generate an implementation of
/// the pliron::Attribute trait and implements other internal traits and types resources required
/// to use the IR attribute.
///
/// Usage:
///
/// ```ignore
/// #[def_attribute]
/// #[attr_name = "my_dialect.attribute"]
/// #[derive(Debug, Clone, PartialEq, Eq)]
/// pub struct StringAttr(String);
/// ```
///
/// **Note**: pre-requisite traits for [Attribute] must already be implemented.
///         Additionaly, PartialEq must be implemented by the type.
#[proc_macro_attribute]
pub fn def_attribute(_args: TokenStream, input: TokenStream) -> TokenStream {
    to_token_stream(derive_attr::def_attribute(input))
}

/// The `#[def_type]` proc macro.
///
/// The macro can be used to annotate a Rust struct as a new IR type.
///
/// The macro will leave the struct definition unchanged, but it will generate an implementation of
/// the pliron::Type trait and implements other internal traits and types resources required
/// to use the IR type.
///
/// Usage:
///
/// ```ignore
/// #[def_type]
/// #[attr_name = "my_dialect.unit"]
/// #[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// pub struct UnitType();
/// ```
///
/// **Note**: pre-requisite traits for [Type] must already be implemented.
///         Additionaly, Hash and Eq must be implemented by the rust type.
#[proc_macro_attribute]
pub fn def_type(_args: TokenStream, input: TokenStream) -> TokenStream {
    to_token_stream(derive_type::def_type(input))
}

/// The `#[def_op]` proc macro.
///
/// The `#[def_op]` can be used to to create a new IR operation.
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
/// #[def_op]
/// #[type_name = "my_dialect.op"]
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
pub fn def_op(_args: TokenStream, input: TokenStream) -> TokenStream {
    to_token_stream(derive_op::def_op(input))
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
