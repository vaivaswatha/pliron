use std::collections::HashSet;

use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::{DeriveInput, Result};

use crate::{
    asmfmt::{Directive, Elem, Input, Lit, Struct, UnnamedVar, Var},
    attr::{AsmFormat, IRKind},
};

pub(crate) fn derive(input: DeriveInput) -> Result<TokenStream> {
    let input = Input::from_syn(&input)?;
    match input {
        Input::Struct(input) => Ok(impl_struct(input)),
    }
}

fn impl_struct(input: Struct) -> TokenStream {
    let name = &input.ident;
    let header = match input.kind {
        IRKind::Type => quote! {
            ::pliron::asmfmt::printers::type_header(self).fmt(ctx, state, fmt)?;
        },
        IRKind::Attribute => quote! {
            ::pliron::asmfmt::printers::attr_header(self).fmt(ctx, state, fmt)?;
        },
        IRKind::Op => quote! {},
    };

    let builder = PrinterBuilder::new(&input.fields);
    let body = builder.build(&input.format);
    quote! {
        impl ::pliron::printable::Printable for #name {
            fn fmt(
                &self,
                ctx: & ::pliron::context::Context,
                state: & ::pliron::printable::State,
                fmt: &mut ::std::fmt::Formatter<'_>,
            ) -> ::std::fmt::Result {
                #header
                #body
                Ok(())
            }
        }
    }
}

struct PrinterBuilder<'a> {
    fields: &'a HashSet<String>,
}

impl<'a> PrinterBuilder<'a> {
    fn new(fields: &'a HashSet<String>) -> Self {
        Self { fields }
    }

    fn build(&self, attr: &AsmFormat) -> TokenStream {
        let elems = attr.format().elems.iter();
        elems.map(|e| self.build_elem(e, true)).collect()
    }

    fn build_elem(&self, elem: &Elem, toplevel: bool) -> TokenStream {
        match elem {
            Elem::Lit(Lit { lit, .. }) => self.build_lit(lit, toplevel),
            Elem::Var(Var { name, .. }) => {
                if self.fields.contains(name) {
                    return self.build_field_use(format_ident!("{}", name), toplevel);
                }
                self.build_attribute_use(name, toplevel)
            }
            Elem::UnnamedVar(UnnamedVar { index, .. }) => {
                self.build_field_use(syn::Index::from(*index), toplevel)
            }
            Elem::Directive(ref d) => self.build_directive(d, toplevel),
        }
    }

    fn build_lit(&self, lit: &str, toplevel: bool) -> TokenStream {
        if toplevel {
            quote! {
                ::pliron::asmfmt::printers::literal(#lit).fmt(ctx, state, fmt)?;
            }
        } else {
            quote! {
                #lit
            }
        }
    }

    fn build_field_use<T>(&self, ident: T, toplevel: bool) -> TokenStream
    where
        T: quote::ToTokens,
    {
        if toplevel {
            quote! {
                ::pliron::asmfmt::printers::print_var!(&self.#ident).fmt(ctx, state, fmt)?;
            }
        } else {
            quote! {
                self.#ident
            }
        }
    }

    fn build_attribute_use(&self, name: &str, toplevel: bool) -> TokenStream {
        let mut printer = quote! {
            ::pliron::asmfmt::printers::get_attr!(self, #name)
        };
        if toplevel {
            printer = quote! { #printer.fmt(ctx, state, fmt)?; };
        }
        printer
    }

    fn build_directive(&self, d: &Directive, toplevel: bool) -> TokenStream {
        let directive = format_ident!("{}_directive", d.name);
        let args = d.args.iter().map(|a| self.build_elem(a, false));
        let mut printer = quote! {
            ::pliron::asmfmt::printers::#directive!(self #(, #args)*)
        };
        if toplevel {
            printer = quote! { #printer.fmt(ctx, state, fmt)?; };
        }
        printer
    }
}
