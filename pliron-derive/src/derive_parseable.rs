use std::collections::BTreeSet;

use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::Result;

use crate::{
    irfmt::{Directive, Elem, FieldIdent, FmtData, Format, IRFmtInput, Lit, UnnamedVar, Var},
    macro_attr::IRKind,
};

pub(crate) fn derive_not_parsable(input: impl Into<TokenStream>) -> Result<TokenStream> {
    let input = syn::parse2::<IRFmtInput>(input.into())?;
    match input.kind {
        IRKind::Type => Ok(emit_not_parsable_type(input.ident)),
        IRKind::Attribute => Ok(emit_not_parsable_attribute(input.ident)),
        IRKind::Op => Ok(emit_not_parsable_op(input.ident)),
    }
}

fn emit_not_parsable_type(name: syn::Ident) -> TokenStream {
    quote! {
        impl ::pliron::parsable::Parsable for #name {
            type Arg = ();
            type Parsed = ::pliron::r#type::TypePtr<Self>;

            fn parse<'a>(
                _state_stream: &mut ::pliron::parsable::StateStream<'a>,
                _arg: Self::Arg,
            ) -> ::pliron::parsable::ParseResult<'a, Self::Parsed>
            where
                Self: Sized,
            {
                todo!()
            }

        }
    }
}

fn emit_not_parsable_attribute(name: syn::Ident) -> TokenStream {
    quote! {
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
    }
}

fn emit_not_parsable_op(name: syn::Ident) -> TokenStream {
    quote! {
        impl ::pliron::parsable::Parsable for #name {
            type Arg = Vec<(::pliron::identifier::Identifier, ::pliron::location::Location)>;
            type Parsed = ::pliron::op::OpObj;

            fn parse<'a>(
                _state_stream: &mut ::pliron::parsable::StateStream<'a>,
                _arg: Self::Arg,
            ) -> ::pliron::parsable::ParseResult<'a, Self::Parsed> {
                todo!()
            }

        }
    }
}

pub(crate) fn derive(input: impl Into<TokenStream>) -> syn::Result<TokenStream> {
    let input = syn::parse2::<IRFmtInput>(input.into())?;
    Ok(impl_parsable(input))
}

fn impl_parsable(input: IRFmtInput) -> TokenStream {
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
            type Parsed = TypePtr<Self>;

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

    fn build(&self, format: &Format) -> TokenStream {
        let elems = format.elems.iter();
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
            ::pliron::irfmt::parsers::literal(#lit).parse_next(state_stream)?;
        }
    }

    fn build_field_use<T>(&self, ident: T, _toplevel: bool) -> TokenStream
    where
        T: quote::ToTokens,
    {
        quote! {
            let #ident = ::pliron::irfmt::parsers::from_parseable().parse_next(state_stream)?.0;
        }
    }

    fn build_attribute_use(&self, _attr: &str, _toplevel: bool) -> TokenStream {
        todo!()
    }

    fn build_directive(&self, _directive: &Directive, _toplevel: bool) -> TokenStream {
        todo!()
    }
}
