mod asmfmt;
mod attr;
mod derive_attr;
mod derive_op;
mod derive_parseable;
mod derive_printable;
mod derive_shared;
mod derive_type;

use proc_macro::TokenStream;
use syn::{parse_macro_input, DeriveInput};

#[proc_macro_attribute]
pub fn def_attribute(_args: TokenStream, input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    to_token_stream(derive_attr::def_attribute(input))
}

#[proc_macro_attribute]
pub fn def_op(_args: TokenStream, input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    to_token_stream(derive_op::def_op(input))
}

#[proc_macro_attribute]
pub fn def_type(_args: TokenStream, input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    to_token_stream(derive_type::def_type(input))
}

#[proc_macro_derive(
    Printable,
    attributes(dialect, ir_kind, type_name, attr_name, asm_format)
)]
pub fn derive_printable(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    to_token_stream(derive_printable::derive(input))
}

#[proc_macro_derive(
    Parsable,
    attributes(dialect, ir_kind, type_name, attr_name, asm_format)
)]
pub fn derive_parsable(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    to_token_stream(derive_parseable::derive(input))
}

#[proc_macro_derive(NotParsableType)]
pub fn derive_not_parsable_type(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    to_token_stream(derive_parseable::derive_not_parsable_type(input))
}

#[proc_macro_derive(NotParsableAttribute)]
pub fn derive_not_parsable_attribute(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    to_token_stream(derive_parseable::derive_not_parsable_attribute(input))
}

pub(crate) fn to_token_stream(res: syn::Result<proc_macro2::TokenStream>) -> TokenStream {
    let tokens = match res {
        Ok(tokens) => tokens,
        Err(error) => to_compile_error(error),
    };
    eprintln!("{}", tokens);
    TokenStream::from(tokens)
}

pub(crate) fn to_compile_error(error: syn::Error) -> proc_macro2::TokenStream {
    let error = error.to_compile_error();
    quote::quote!(
        #error
    )
}

#[proc_macro_derive(DeriveAttribDummy, attributes(dialect, ir_kind))]
pub fn derive_attrib_dummy(_input: TokenStream) -> TokenStream {
    TokenStream::new()
}
