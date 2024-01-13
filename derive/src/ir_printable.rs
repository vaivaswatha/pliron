use std::collections::BTreeSet;

use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use syn::{DeriveInput, Result};

use crate::{
    asmfmt::{Directive, Elem, FieldIdent, Format, Input, Lit, Optional, Struct, UnnamedVar, Var},
    attr::{AsmFormat, IRKind},
};

pub(crate) fn derive(input: DeriveInput) -> Result<TokenStream> {
    let input = Input::from_syn(&input)?;
    match input {
        Input::Struct(input) => impl_struct(input),
    }
}

fn impl_struct(input: Struct) -> Result<TokenStream> {
    let name = &input.ident;
    let body = match input.kind {
        IRKind::Type | IRKind::Attribute => {
            AttribTypePrinterBuilder2::new(input.ident.span(), &input.fields)
                .build(&input.format)?
        }
        IRKind::Op => OpPrinterBuilder::new(&input.fields).build(&input.format),
    };
    Ok(quote! {
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
    })
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

    fn build(&self, attr: &AsmFormat) -> TokenStream {
        self.build_format(attr.format(), true)
    }

    fn build_format(&self, format: &Format, toplevel: bool) -> TokenStream {
        let elems = format.elems.iter();
        elems.map(|e| self.build_elem(e, toplevel)).collect()
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
                #ident
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

    fn build_var(&self, name: &str, toplevel: bool) -> TokenStream {
        let ident = FieldIdent::Named(name.into());
        if self.fields.contains(&ident) {
            return self.build_field_use(ident, toplevel);
        }
        self.build_attribute_use(name, toplevel)
    }

    fn build_unnamed_var(&self, index: usize, toplevel: bool) -> TokenStream {
        self.build_field_use(syn::Index::from(index), toplevel)
    }

    fn build_directive(&self, d: &Directive, toplevel: bool) -> TokenStream {
        let directive = format_ident!("op_{}_directive", d.name);
        let args = d.args.iter().map(|a| self.build_elem(a, false));
        let mut printer = quote! {
            ::pliron::asmfmt::printers::#directive!(ctx, self #(, #args)*)
        };
        if toplevel {
            printer = quote! { #printer.fmt(ctx, state, fmt)?; };
        }
        printer
    }

    fn build_optional(&self, d: &Optional, toplevel: bool) -> TokenStream {
        let check = Directive::new_with_args("check", vec![d.check.as_ref().clone()]);

        let check = self.build_directive(&check, false);
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

struct AttribTypePrinterBuilder2<'a> {
    span: Span,
    fields: &'a [FieldIdent],
}

#[derive(Debug)]
enum ATValue {
    Stream(TokenStream),
    Fields(Vec<FieldIdent>),
    Lit(String),
}

impl From<TokenStream> for ATValue {
    fn from(stream: TokenStream) -> Self {
        Self::Stream(stream)
    }
}

impl From<Vec<FieldIdent>> for ATValue {
    fn from(fields: Vec<FieldIdent>) -> Self {
        Self::Fields(fields)
    }
}

impl From<String> for ATValue {
    fn from(lit: String) -> Self {
        Self::Lit(lit)
    }
}

impl<'a> AttribTypePrinterBuilder2<'a> {
    fn new(span: Span, fields: &'a [FieldIdent]) -> Self {
        Self { span, fields }
    }

    fn build(&self, attr: &AsmFormat) -> syn::Result<TokenStream> {
        self.build_format(attr.format(), true)
    }

    fn build_format(&self, format: &Format, toplevel: bool) -> syn::Result<TokenStream> {
        let elems = format.elems.iter();
        elems
            .map(|e| match self.build_elem(e, toplevel)? {
                ATValue::Stream(stream) => Ok(stream),
                ATValue::Fields(fields) => Err(syn::Error::new(
                    self.span,
                    format!("expected a literal, found `{:?}`", fields),
                )),
                ATValue::Lit(lit) => Ok(quote! {
                    #lit.fmt(ctx, state, fmt)?;
                }),
            })
            .collect()
    }

    fn build_elem(&self, elem: &Elem, toplevel: bool) -> syn::Result<ATValue> {
        match elem {
            Elem::Lit(Lit { lit, .. }) => self.build_lit(lit, toplevel),
            Elem::Var(Var { name, .. }) => self.build_var(name, toplevel),
            Elem::UnnamedVar(UnnamedVar { index, .. }) => self.build_unnamed_var(*index, toplevel),
            Elem::Directive(ref d) => self.build_directive(d, toplevel),
            Elem::Optional(ref opt) => self.build_optional(opt, toplevel),
        }
    }

    fn build_lit(&self, lit: &str, toplevel: bool) -> syn::Result<ATValue> {
        if toplevel {
            Ok(quote! {
                #lit.fmt(ctx, state, fmt)?;
            }
            .into())
        } else {
            Ok(lit.to_string().into())
        }
    }

    fn build_var(&self, name: &str, toplevel: bool) -> syn::Result<ATValue> {
        if toplevel {
            let ident = format_ident!("{}", name);
            Ok(quote! {
                ::pliron::asmfmt::printers::print_var!(&self.#ident).fmt(ctx, state, fmt)?;
            }
            .into())
        } else {
            Ok(ATValue::Fields(vec![name.into()]))
        }
    }

    fn build_unnamed_var(&self, index: usize, toplevel: bool) -> syn::Result<ATValue> {
        if toplevel {
            let ident = syn::Index::from(index);
            Ok(quote! {
                ::pliron::asmfmt::printers::print_var!(&self.#ident).fmt(ctx, state, fmt)?;
            }
            .into())
        } else {
            Ok(ATValue::Fields(vec![index.into()]))
        }
    }

    fn build_directive(&self, d: &Directive, toplevel: bool) -> syn::Result<ATValue> {
        match d.name.as_str() {
            "params" => {
                require_no_args(self.span, "params", &d.args)?;
                if toplevel {
                    let args = quote! { () };
                    Ok(self.build_call_toplevel_directive(d, args).into())
                } else {
                    Ok(ATValue::Fields(self.fields.iter().cloned().collect()))
                }
            }
            "struct" => {
                require_toplevel(self.span, "struct", toplevel)?;
                require_args(self.span, "struct", &d.args)?;
                let args = self.build_arg_fields(&d.args)?;
                let args = self.args_to_token_streams(&args);
                Ok(self.build_call_toplevel_directive(d, args).into())
            }
            "qualifier" => {
                require_toplevel(self.span, "qualifier", toplevel)?;
                let args = quote! { () };
                Ok(self.build_call_toplevel_directive(d, args).into())
            }
            _ => {
                // custom directives are allowed at the top-level
                require_toplevel(self.span, &d.name, toplevel)?;
                let args = self.build_arg_fields(&d.args)?;
                let args = self.args_to_token_streams(&args);
                Ok(self.build_call_toplevel_directive(d, args).into())
            }
        }
    }

    fn build_call_toplevel_directive(&self, d: &Directive, args: TokenStream) -> TokenStream {
        let printer_args = quote! { (ctx, state, fmt) };
        let field_names = self.fields;
        let directive = format_ident!("at_{}_directive", d.name);
        quote! {
            ::pliron::asmfmt::printers::#directive!(self, #printer_args, #args, (#(#field_names)*));
        }
    }

    fn build_arg_fields(&self, args: &[Elem]) -> syn::Result<Vec<ATValue>> {
        let mut fields = vec![];
        for (i, arg) in args.iter().enumerate() {
            let v = self.build_elem(arg, false)?;
            match v {
                ATValue::Stream(_) => {
                    return Err(syn::Error::new(
                        self.span,
                        format!("argument {} is not a valid argument", i),
                    ))
                }
                _ => fields.push(v),
            }
        }
        Ok(fields)
    }

    fn args_to_token_streams(&self, args: &[ATValue]) -> TokenStream {
        let mut streams = vec![];
        for arg in args {
            match arg {
                ATValue::Stream(_) => unreachable!(),
                ATValue::Fields(fields) => {
                    streams.extend(fields.iter().map(|f| {
                        quote! { #f }
                    }));
                }
                ATValue::Lit(lit) => {
                    streams.push(quote! { #lit });
                }
            }
        }
        quote! {
            (#(#streams),*)
        }
    }

    fn build_optional(&self, d: &Optional, toplevel: bool) -> syn::Result<ATValue> {
        require_toplevel(self.span, "optional", toplevel).unwrap();

        let check = Directive::new_with_args("check", vec![d.check.as_ref().clone()]);

        let check = require_tokenstream(self.span, self.build_directive(&check, false)?)?;
        let then_block = self.build_format(&d.then_format, toplevel)?;
        if let Some(else_format) = &d.else_format {
            let else_block = self.build_format(else_format, toplevel)?;
            Ok(quote! {
                if #check {
                    #then_block
                } else {
                    #else_block
                }
            }
            .into())
        } else {
            Ok(quote! {
                if #check {
                    #then_block
                }
            }
            .into())
        }
    }
}

fn require_toplevel(span: Span, directive: &str, toplevel: bool) -> syn::Result<()> {
    if !toplevel {
        return Err(syn::Error::new(
            span,
            format!("`{}` directive is only allowed at the top-level", directive),
        ));
    }
    Ok(())
}

fn require_no_args(span: Span, directive: &str, args: &[Elem]) -> syn::Result<()> {
    if !args.is_empty() {
        return Err(syn::Error::new(
            span,
            format!("`{}` directive does not take any arguments", directive),
        ));
    }
    Ok(())
}

fn require_args(span: Span, directive: &str, args: &[Elem]) -> syn::Result<()> {
    if args.is_empty() {
        return Err(syn::Error::new(
            span,
            format!("`{}` directive requires arguments", directive),
        ));
    }
    Ok(())
}

fn require_tokenstream(span: Span, val: ATValue) -> syn::Result<TokenStream> {
    match val {
        ATValue::Stream(stream) => Ok(stream),
        ATValue::Fields(fields) => Err(syn::Error::new(
            span,
            format!("expected a literal, found `{:?}`", fields),
        )),
        ATValue::Lit(lit) => Ok(quote! {
            #lit.fmt(ctx, state, fmt)?
        }),
    }
}
