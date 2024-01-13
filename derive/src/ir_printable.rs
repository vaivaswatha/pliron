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
            AttribTypePrinterBuilder::new(input.ident.span(), &input.fields).build(&input.format)
        }
        IRKind::Op => OpPrinterBuilder::new(input.ident.span(), &input.fields).build(&input.format),
    }?;
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

trait PrinterBuilder {
    fn build(&self, attr: &AsmFormat) -> Result<TokenStream> {
        self.build_format(attr.format(), true)
    }

    fn span(&self) -> Span;

    fn finalize_toplevel(&self, value: PValue) -> Result<TokenStream>;

    fn build_lit(&self, lit: &str, toplevel: bool) -> syn::Result<PValue>;

    fn build_var(&self, name: &str, toplevel: bool) -> syn::Result<PValue>;

    fn build_unnamed_var(&self, index: usize, toplevel: bool) -> syn::Result<PValue>;

    fn build_directive(&self, d: &Directive, toplevel: bool) -> syn::Result<PValue>;

    fn build_check(&self, check: &Elem) -> Result<TokenStream> {
        let check = Directive::new_with_args("check", vec![check.clone()]);
        let val = self.build_directive(&check, false)?;
        match val {
            PValue::Stream(stream) => Ok(stream),
            PValue::Fields(fields) => Err(syn::Error::new(
                self.span(),
                format!("expected a literal, found `{:?}`", fields),
            )),
            PValue::Lit(lit) => Ok(make_print(quote! { #lit })),
        }
    }

    fn build_format(&self, format: &Format, toplevel: bool) -> Result<TokenStream> {
        format
            .elems
            .iter()
            .map(|e| self.finalize_toplevel(self.build_elem(e, toplevel)?))
            .collect()
    }

    fn build_elem(&self, elem: &Elem, toplevel: bool) -> Result<PValue> {
        match elem {
            Elem::Lit(Lit { lit, .. }) => self.build_lit(lit, toplevel),
            Elem::Var(Var { name, .. }) => self.build_var(name, toplevel),
            Elem::UnnamedVar(UnnamedVar { index, .. }) => self.build_unnamed_var(*index, toplevel),
            Elem::Directive(ref d) => self.build_directive(d, toplevel),
            Elem::Optional(ref opt) => self.build_optional(opt, toplevel),
        }
    }

    fn build_optional(&self, d: &Optional, toplevel: bool) -> Result<PValue> {
        require_toplevel(self.span(), "optional", toplevel).unwrap();

        let check = self.build_check(&d.check)?;
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

#[derive(Debug)]
enum PValue {
    Stream(TokenStream),
    Fields(Vec<FieldIdent>),
    Lit(String),
}

impl From<TokenStream> for PValue {
    fn from(stream: TokenStream) -> Self {
        Self::Stream(stream)
    }
}

impl From<Vec<FieldIdent>> for PValue {
    fn from(fields: Vec<FieldIdent>) -> Self {
        Self::Fields(fields)
    }
}

impl From<String> for PValue {
    fn from(lit: String) -> Self {
        Self::Lit(lit)
    }
}

struct OpPrinterBuilder {
    span: Span,
    fields: BTreeSet<FieldIdent>,
}

impl OpPrinterBuilder {
    fn new(span: Span, fields: &[FieldIdent]) -> Self {
        Self {
            span,
            fields: BTreeSet::from_iter(fields.iter().cloned()),
        }
    }
}

impl PrinterBuilder for OpPrinterBuilder {
    fn span(&self) -> Span {
        self.span
    }

    fn finalize_toplevel(&self, value: PValue) -> Result<TokenStream> {
        match value {
            PValue::Stream(stream) => Ok(stream),
            PValue::Fields(fields) => Err(syn::Error::new(
                self.span,
                format!("expected a literal, found `{:?}`", fields),
            )),
            PValue::Lit(lit) => Ok(make_print(quote! {
                ::pliron::asmfmt::printers::literal(#lit)
            })),
        }
    }

    fn build_lit(&self, lit: &str, toplevel: bool) -> Result<PValue> {
        let toks = if toplevel {
            make_print(quote! {
                ::pliron::asmfmt::printers::literal(#lit)
            })
        } else {
            quote! { #lit }
        };
        Ok(toks.into())
    }

    fn build_var(&self, name: &str, toplevel: bool) -> Result<PValue> {
        let ident = FieldIdent::Named(name.into());
        if self.fields.contains(&ident) {
            return Ok(self.build_field_use(ident, toplevel).into());
        }
        Ok(self.build_attribute_use(name, toplevel).into())
    }

    fn build_unnamed_var(&self, index: usize, toplevel: bool) -> Result<PValue> {
        Ok(self
            .build_field_use(syn::Index::from(index), toplevel)
            .into())
    }

    fn build_directive(&self, d: &Directive, toplevel: bool) -> Result<PValue> {
        let directive = format_ident!("op_{}_directive", d.name);
        let args = d
            .args
            .iter()
            .map(|a| match self.build_elem(a, false)? {
                PValue::Stream(stream) => Ok(stream),
                PValue::Fields(fields) => Err(syn::Error::new(
                    self.span(),
                    format!("expected tokens, but found struct fields `{:?}`", fields),
                )),
                PValue::Lit(lit) => Err(syn::Error::new(
                    self.span(),
                    format!("expected a tokens, but found a string value `{}`", lit),
                )),
            })
            .collect::<Result<Vec<_>>>()?;
        let printer = quote! {
            ::pliron::asmfmt::printers::#directive!(ctx, self #(, #args)*)
        };
        Ok(make_print_if(toplevel, printer).into())
    }
}

impl OpPrinterBuilder {
    fn build_field_use<T>(&self, ident: T, toplevel: bool) -> TokenStream
    where
        T: quote::ToTokens,
    {
        if toplevel {
            make_print(quote! {
                ::pliron::asmfmt::printers::print_var!(&self.#ident)
            })
        } else {
            quote! {
                #ident
            }
        }
    }

    fn build_attribute_use(&self, name: &str, toplevel: bool) -> TokenStream {
        let printer = quote! {
            ::pliron::asmfmt::printers::get_attr!(self, #name)
        };
        make_print_if(toplevel, printer)
    }
}

struct AttribTypePrinterBuilder<'a> {
    span: Span,
    fields: &'a [FieldIdent],
}

impl<'a> AttribTypePrinterBuilder<'a> {
    fn new(span: Span, fields: &'a [FieldIdent]) -> Self {
        Self { span, fields }
    }
}

impl<'a> PrinterBuilder for AttribTypePrinterBuilder<'a> {
    fn span(&self) -> Span {
        self.span
    }

    fn finalize_toplevel(&self, value: PValue) -> Result<TokenStream> {
        match value {
            PValue::Stream(stream) => Ok(stream),
            PValue::Fields(fields) => Err(syn::Error::new(
                self.span,
                format!("expected a literal, found `{:?}`", fields),
            )),
            PValue::Lit(lit) => Ok(make_print(quote! { #lit })),
        }
    }

    fn build_lit(&self, lit: &str, toplevel: bool) -> syn::Result<PValue> {
        if toplevel {
            Ok(make_print(quote! { #lit }).into())
        } else {
            Ok(lit.to_string().into())
        }
    }

    fn build_var(&self, name: &str, toplevel: bool) -> syn::Result<PValue> {
        if toplevel {
            let ident = format_ident!("{}", name);
            Ok(make_print(quote! {
                ::pliron::asmfmt::printers::print_var!(&self.#ident)
            })
            .into())
        } else {
            Ok(PValue::Fields(vec![name.into()]))
        }
    }

    fn build_unnamed_var(&self, index: usize, toplevel: bool) -> syn::Result<PValue> {
        if toplevel {
            let ident = syn::Index::from(index);
            Ok(make_print(quote! {
                ::pliron::asmfmt::printers::print_var!(&self.#ident)
            })
            .into())
        } else {
            Ok(PValue::Fields(vec![index.into()]))
        }
    }

    fn build_directive(&self, d: &Directive, toplevel: bool) -> syn::Result<PValue> {
        match d.name.as_str() {
            "params" => {
                require_no_args(self.span, "params", &d.args)?;
                if toplevel {
                    let args = quote! { () };
                    Ok(self.build_call_toplevel_directive(d, args).into())
                } else {
                    Ok(PValue::Fields(self.fields.iter().cloned().collect()))
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
}

impl<'a> AttribTypePrinterBuilder<'a> {
    fn build_call_toplevel_directive(&self, d: &Directive, args: TokenStream) -> TokenStream {
        let printer_args = quote! { (ctx, state, fmt) };
        let field_names = self.fields;
        let directive = format_ident!("at_{}_directive", d.name);
        quote! {
            ::pliron::asmfmt::printers::#directive!(self, #printer_args, #args, (#(#field_names)*));
        }
    }

    fn build_arg_fields(&self, args: &[Elem]) -> syn::Result<Vec<PValue>> {
        let mut fields = vec![];
        for (i, arg) in args.iter().enumerate() {
            let v = self.build_elem(arg, false)?;
            match v {
                PValue::Stream(_) => {
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

    fn args_to_token_streams(&self, args: &[PValue]) -> TokenStream {
        let mut streams = vec![];
        for arg in args {
            match arg {
                PValue::Stream(_) => unreachable!(),
                PValue::Fields(fields) => {
                    streams.extend(fields.iter().map(|f| {
                        quote! { #f }
                    }));
                }
                PValue::Lit(lit) => {
                    streams.push(quote! { #lit });
                }
            }
        }
        quote! {
            (#(#streams),*)
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
