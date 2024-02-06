use std::collections::BTreeSet;

use proc_macro2::TokenStream;
use quote::{format_ident, quote, ToTokens};
use syn::Result;

use crate::{
    irfmt::{
        AttribTypeFmtEvaler, Directive, Elem, FieldIdent, FmtData, Format, IRFmtInput, Lit,
        Optional, UnnamedVar, Var,
    },
    macro_attr::IRKind,
};

pub(crate) fn derive(input: impl Into<TokenStream>) -> Result<TokenStream> {
    let input = syn::parse2::<IRFmtInput>(input.into())?;
    let p = DerivedPrinter::try_from(input)?;
    Ok(p.into_token_stream())
}

enum DerivedPrinter {
    AttribType(DerivedAttribTypePrinter),
    Op(DerivedOpPrinter),
}

impl TryFrom<IRFmtInput> for DerivedPrinter {
    type Error = syn::Error;

    fn try_from(input: IRFmtInput) -> Result<Self> {
        match input.kind {
            IRKind::Type | IRKind::Attribute => {
                DerivedAttribTypePrinter::try_from(input).map(Self::AttribType)
            }
            IRKind::Op => Ok(Self::Op(DerivedOpPrinter::from(input))),
        }
    }
}

impl ToTokens for DerivedPrinter {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            Self::AttribType(p) => p.to_tokens(tokens),
            Self::Op(p) => p.to_tokens(tokens),
        }
    }
}

struct DerivedAttribTypePrinter {
    ident: syn::Ident,
    format: Format,
    fields: Vec<FieldIdent>,
}

impl TryFrom<IRFmtInput> for DerivedAttribTypePrinter {
    type Error = syn::Error;

    fn try_from(input: IRFmtInput) -> Result<Self> {
        let fields = match input.data {
            FmtData::Struct(s) => s.fields,
        };
        let evaler = AttribTypeFmtEvaler::new(input.ident.span(), &fields);
        let format = evaler.eval(input.format.into_format())?;
        Ok(Self {
            ident: input.ident,
            format,
            fields,
        })
    }
}

impl ToTokens for DerivedAttribTypePrinter {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let builder = AttribTypePrinterBuilder::new(&self.fields);
        tokens.extend(builder.build(&self.ident, &self.format));
    }
}

struct AttribTypePrinterBuilder<'a> {
    fields: &'a [FieldIdent],
}

impl<'a> AttribTypePrinterBuilder<'a> {
    fn new(fields: &'a [FieldIdent]) -> Self {
        Self { fields }
    }
}

impl<'a> PrinterBuilder for AttribTypePrinterBuilder<'a> {
    fn build_directive(&self, d: &Directive, _toplevel: bool) -> TokenStream {
        let printer_args = quote! { (ctx, state, fmt) };
        let field_names = self.fields;
        let args = d.args.iter().map(|e| self.build_elem(e, false));
        let directive = format_ident!("at_{}_directive", d.name);
        quote! {
            ::pliron::irfmt::printers::#directive!(self, #printer_args, (#(#args),*), (#(#field_names)*));
        }
    }
}

struct DerivedOpPrinter {
    ident: syn::Ident,
    format: Format,
    fields: Vec<FieldIdent>,
}

impl From<IRFmtInput> for DerivedOpPrinter {
    fn from(input: IRFmtInput) -> Self {
        let fields = match input.data {
            FmtData::Struct(s) => s.fields,
        };
        Self {
            ident: input.ident,
            format: input.format.into_format(),
            fields,
        }
    }
}

impl ToTokens for DerivedOpPrinter {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let builder = OpPrinterBuilder::new(&self.fields);
        tokens.extend(builder.build(&self.ident, &self.format));
    }
}

struct OpPrinterBuilder {
    fields: BTreeSet<FieldIdent>,
}

impl OpPrinterBuilder {
    fn new(fields: &[FieldIdent]) -> Self {
        Self {
            fields: BTreeSet::from_iter(fields.iter().cloned()),
        }
    }
}

impl PrinterBuilder for OpPrinterBuilder {
    fn build_var(&self, name: &str, toplevel: bool) -> TokenStream {
        let ident = FieldIdent::Named(name.into());
        if self.fields.contains(&ident) {
            return self.build_field_use(ident, toplevel);
        }

        make_print_if(
            toplevel,
            quote! {
                ::pliron::irfmt::printers::get_attr!(self, #name)
            },
        )
    }

    fn build_directive(&self, d: &Directive, toplevel: bool) -> TokenStream {
        let directive = format_ident!("op_{}_directive", d.name);
        let args = d.args.iter().map(|e| self.build_elem(e, false));
        let printer = quote! {
            ::pliron::irfmt::printers::#directive!(ctx, self #(, #args)*)
        };
        make_print_if(toplevel, printer)
    }
}

trait PrinterBuilder {
    fn build_directive(&self, d: &Directive, toplevel: bool) -> TokenStream;

    fn build(&self, name: &syn::Ident, attr: &Format) -> TokenStream {
        let body = self.build_body(attr);
        quote! {
            impl ::pliron::printable::Printable for #name {
                fn fmt(
                    &self,
                    ctx: & ::pliron::context::Context,
                    state: & ::pliron::printable::State,
                    fmt: &mut ::std::fmt::Formatter<'_>,
                ) -> ::std::fmt::Result {
                    #body
                    Ok(())
                }
            }
        }
    }

    fn build_body(&self, attr: &Format) -> TokenStream {
        self.build_format(attr, true)
    }

    fn build_lit(&self, lit: &str, toplevel: bool) -> TokenStream {
        if toplevel {
            make_print(quote! {
                ::pliron::irfmt::printers::literal(#lit)
            })
        } else {
            quote! { #lit }
        }
    }

    fn build_var(&self, name: &str, toplevel: bool) -> TokenStream {
        self.build_field_use(format_ident!("{}", name), toplevel)
    }

    fn build_unnamed_var(&self, index: usize, toplevel: bool) -> TokenStream {
        self.build_field_use(syn::Index::from(index), toplevel)
    }

    fn build_field_use<T>(&self, ident: T, toplevel: bool) -> TokenStream
    where
        T: quote::ToTokens,
    {
        if toplevel {
            make_print(quote! {
                ::pliron::irfmt::printers::print_var!(&self.#ident)
            })
        } else {
            quote! {
                #ident
            }
        }
    }

    fn build_check(&self, check: &Elem) -> TokenStream {
        let check = Directive::new_with_args("check", vec![check.clone()]);
        self.build_directive(&check, false)
    }

    fn build_format(&self, format: &Format, toplevel: bool) -> TokenStream {
        TokenStream::from_iter(
            format
                .elems
                .iter()
                .map(|elem| self.build_elem(elem, toplevel)),
        )
    }

    fn build_elem(&self, elem: &Elem, toplevel: bool) -> TokenStream {
        match elem {
            Elem::Lit(Lit { lit, .. }) => self.build_lit(lit, toplevel),
            Elem::Var(Var { name, .. }) => self.build_var(name, toplevel),
            Elem::UnnamedVar(UnnamedVar { index, .. }) => self.build_unnamed_var(*index, toplevel),
            Elem::Directive(ref d) => self.build_directive(d, toplevel),
            Elem::Optional(ref opt) => self.build_optional(opt, toplevel),
        }
    }

    fn build_optional(&self, d: &Optional, toplevel: bool) -> TokenStream {
        let check = self.build_check(&d.check);
        let then_block = self.build_format(&d.then_format, toplevel);
        if let Some(else_format) = &d.else_format {
            let else_block = self.build_format(else_format, toplevel);
            quote! {
                if #check {
                    #then_block
                } else {
                    #else_block
                }
            }
        } else {
            quote! {
                if #check {
                    #then_block
                }
            }
        }
    }
}

fn make_print(stmt: TokenStream) -> TokenStream {
    quote! {
        #stmt.fmt(ctx, state, fmt)?;
    }
}

fn make_print_if(cond: bool, stmt: TokenStream) -> TokenStream {
    if cond {
        make_print(stmt)
    } else {
        stmt
    }
}
