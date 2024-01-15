use std::collections::BTreeSet;

use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::{DeriveInput, Result};

use crate::{
    asmfmt::{AsmFmtInput, Directive, Elem, FieldIdent, FmtData, Lit, UnnamedVar, Var},
    attr::AsmFormat,
};

pub(crate) fn derive_not_parsable_type(input: impl Into<TokenStream>) -> Result<TokenStream> {
    let input = syn::parse2::<DeriveInput>(input.into())?;
    let name = input.ident;
    Ok(quote! {
        impl ::pliron::parsable::Parsable for #name {
            type Arg = ();
            type Parsed = ::pliron::context::Ptr<::pliron::r#type::TypeObj>;

            fn parse<'a>(
                _state_stream: &mut ::pliron::parsable::StateStream<'a>,
                _arg: Self::Arg,
            ) -> ::pliron::parsable::ParseResult<'a, Self::Parsed> {
                todo!()
            }

        }
    })
}

pub(crate) fn derive_not_parsable_attribute(input: impl Into<TokenStream>) -> Result<TokenStream> {
    let input = syn::parse2::<DeriveInput>(input.into())?;
    let name = input.ident;
    Ok(quote! {
        impl ::pliron::parsable::Parsable for #name {
            type Arg = ();
            type Parsed = ::pliron::attribute::AttrObj;

            fn parse<'a>(
                _state_stream: &mut ::pliron::parsable::StateStream<'a>,
                _arg: Self::Arg,
            ) -> ::pliron::parsable::ParseResult<'a, Self::Parsed> {
                todo!()
            }

        }
    })
}

pub(crate) fn derive(input: impl Into<TokenStream>) -> syn::Result<TokenStream> {
    let input = syn::parse2::<AsmFmtInput>(input.into())?;
    Ok(impl_parsable(input))
}

fn impl_parsable(input: AsmFmtInput) -> TokenStream {
    let name = &input.ident;

    let (init_self, body) = match input.data {
        FmtData::Struct(s) => {
            let builder = ParserBuilder::new(&s.fields);
            let body = builder.build(&input.format);
            let init_fields = &s.fields;
            let init_self = quote! {
                Self {
                    #(#init_fields),*
                }
            };
            (init_self, body)
        }
    };

    quote! {
        impl ::pliron::parsable::Parsable for #name {
            type Arg = ();
            type Parsed = Ptr<TypeObj>;

            fn parse<'a>(
                state_stream: &mut StateStream<'a>,
                _arg: Self::Arg,
            ) -> ParseResult<'a, Self::Parsed> {
                #body
                Ok((
                    ::pliron::r#type::Type::register_instance(#init_self, state_stream.state.ctx),
                    Commit::Commit(()),
                ))
            }
        }
    }
}

struct ParserBuilder {
    fields: BTreeSet<FieldIdent>,
}

impl ParserBuilder {
    fn new(fields: &[FieldIdent]) -> Self {
        Self {
            fields: BTreeSet::from_iter(fields.iter().cloned()),
        }
    }

    fn build(&self, attr: &AsmFormat) -> TokenStream {
        let elems = attr.format().elems.iter();
        elems.map(|e| self.build_elem(e, true)).collect()
    }

    fn build_elem(&self, elem: &Elem, toplevel: bool) -> TokenStream {
        match elem {
            Elem::Lit(Lit { lit, .. }) => self.build_lit(lit, toplevel),
            Elem::Var(Var { name, .. }) => {
                let ident = FieldIdent::Named(name.clone());
                if self.fields.contains(&ident) {
                    return self.build_field_use(format_ident!("{}", name), toplevel);
                }
                self.build_attribute_use(name, toplevel)
            }
            Elem::UnnamedVar(UnnamedVar { index, .. }) => {
                self.build_field_use(FieldIdent::Unnamed(*index), toplevel)
            }
            Elem::Directive(ref d) => self.build_directive(d, toplevel),
            Elem::Optional(ref _opt) => {
                todo!()
            }
        }
    }

    fn build_lit(&self, lit: &str, _toplevel: bool) -> TokenStream {
        quote! {
            ::pliron::asmfmt::parsers::literal(#lit).parse_next(state_stream)?;
        }
    }

    fn build_field_use<T>(&self, ident: T, _toplevel: bool) -> TokenStream
    where
        T: quote::ToTokens,
    {
        quote! {
            let #ident = ::pliron::asmfmt::parsers::from_parseable().parse_next(state_stream)?.0;
        }
    }

    fn build_attribute_use(&self, _attr: &str, _toplevel: bool) -> TokenStream {
        todo!()
    }

    fn build_directive(&self, _directive: &Directive, _toplevel: bool) -> TokenStream {
        todo!()
    }
}
