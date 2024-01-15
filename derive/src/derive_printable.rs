use std::collections::BTreeSet;

use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use syn::Result;

use crate::{
    asmfmt::{
        AsmFmtInput, Directive, Elem, FieldIdent, Format, Lit, Optional, Struct, UnnamedVar, Var,
    },
    attr::{AsmFormat, IRKind},
};

pub(crate) fn derive(input: impl Into<TokenStream>) -> Result<TokenStream> {
    match syn::parse2::<AsmFmtInput>(input.into())? {
        AsmFmtInput::Struct(input) => impl_struct(input),
    }
}

fn impl_struct(input: Struct) -> Result<TokenStream> {
    let name = &input.ident;
    let span = input.ident.span();
    let body = match input.kind {
        IRKind::Type | IRKind::Attribute => {
            let evaler = AttribTypeFmtEvaler::new(span, &input.fields);
            let f = evaler.eval(input.format)?;
            AttribTypePrinterBuilder::new(&input.fields).build(&f)
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

trait PrinterBuilder {
    fn build(&self, attr: &AsmFormat) -> TokenStream {
        self.build_format(attr.format(), true)
    }

    fn build_lit(&self, lit: &str, toplevel: bool) -> TokenStream {
        make_print_if(toplevel, quote! { #lit })
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
                ::pliron::asmfmt::printers::print_var!(&self.#ident)
            })
        } else {
            quote! {
                #ident
            }
        }
    }

    fn build_directive(&self, d: &Directive, toplevel: bool) -> TokenStream;

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
                ::pliron::asmfmt::printers::get_attr!(self, #name)
            },
        )
    }

    fn build_directive(&self, d: &Directive, toplevel: bool) -> TokenStream {
        let directive = format_ident!("op_{}_directive", d.name);
        let args = d.args.iter().map(|e| self.build_elem(e, false));
        let printer = quote! {
            ::pliron::asmfmt::printers::#directive!(ctx, self #(, #args)*)
        };
        make_print_if(toplevel, printer)
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
            ::pliron::asmfmt::printers::#directive!(self, #printer_args, (#(#args),*), (#(#field_names)*));
        }
    }
}

struct FmtValue(Vec<Elem>);

impl From<Elem> for FmtValue {
    fn from(elem: Elem) -> Self {
        Self(vec![elem])
    }
}

impl From<Vec<Elem>> for FmtValue {
    fn from(elems: Vec<Elem>) -> Self {
        Self(elems)
    }
}

impl From<Directive> for FmtValue {
    fn from(d: Directive) -> Self {
        Self(vec![Elem::Directive(d)])
    }
}

impl From<Optional> for FmtValue {
    fn from(opt: Optional) -> Self {
        Self(vec![Elem::Optional(opt)])
    }
}

impl From<FmtValue> for Vec<Elem> {
    fn from(value: FmtValue) -> Self {
        value.0
    }
}

impl From<FmtValue> for Format {
    fn from(value: FmtValue) -> Self {
        Self { elems: value.0 }
    }
}

impl FmtValue {
    // flattens a FmtValue such that it contains no nested Values.
    fn flatten(self) -> Vec<Elem> {
        self.0
    }

    fn len(&self) -> usize {
        self.0.len()
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn flatten_into(self, values: &mut Vec<Elem>) {
        values.extend(self.0);
    }

    fn into_iter(self) -> impl Iterator<Item = Elem> {
        self.0.into_iter()
    }
}

struct AttribTypeFmtEvaler<'a> {
    span: Span,
    fields: &'a [FieldIdent],
}

impl<'a> AttribTypeFmtEvaler<'a> {
    fn new(span: Span, fields: &'a [FieldIdent]) -> Self {
        Self { span, fields }
    }

    fn span(&self) -> Span {
        self.span
    }

    fn eval(&self, f: AsmFormat) -> Result<AsmFormat> {
        Ok(self.eval_format(f.into_format(), true)?.into())
    }

    fn eval_format(&self, f: Format, toplevel: bool) -> Result<Format> {
        let elems = self.eval_elems(f.elems, toplevel)?;
        Ok(elems.into())
    }

    fn eval_elems(&self, elem: Vec<Elem>, toplevel: bool) -> Result<FmtValue> {
        let results = elem.into_iter().map(|e| self.eval_elem(e, toplevel));
        let mut elems = vec![];
        for r in results {
            r?.flatten_into(&mut elems);
        }
        Ok(FmtValue(elems))
    }

    fn eval_elem(&self, elem: Elem, toplevel: bool) -> Result<FmtValue> {
        match elem {
            Elem::Lit(_) | Elem::Var(_) | Elem::UnnamedVar(_) => Ok(elem.into()),
            Elem::Directive(d) => self.eval_directive(d, toplevel),
            Elem::Optional(opt) => self.eval_optional(opt, toplevel),
        }
    }

    fn eval_directive(&self, d: Directive, toplevel: bool) -> Result<FmtValue> {
        match d.name.as_str() {
            "params" => {
                require_no_args(self.span, "params", &d.args)?;
                if toplevel {
                    Ok(FmtValue::from(d))
                } else {
                    Ok(FmtValue::from(
                        self.fields.iter().map(|f| f.into()).collect::<Vec<_>>(),
                    ))
                }
            }
            "struct" => {
                require_toplevel(self.span, &d.name, toplevel)?;
                require_args(self.span, "struct", &d.args)?;
                let args = self.eval_args(d.args)?;
                Ok(FmtValue::from(Directive { args, ..d }))
            }
            _ => {
                require_toplevel(self.span, &d.name, toplevel)?;
                let args = self.eval_args(d.args)?;
                Ok(FmtValue::from(Directive { args, ..d }))
            }
        }
    }

    fn eval_args(&self, args: Vec<Elem>) -> Result<Vec<Elem>> {
        let values = self.eval_elems(args, false)?;
        Ok(values.into())
    }

    fn eval_optional(&self, opt: Optional, toplevel: bool) -> Result<FmtValue> {
        require_toplevel(self.span(), "optional", toplevel).unwrap();

        let mut check_tmp = self.eval_elem(*opt.check, false)?.flatten();
        let Some(check) = check_tmp.pop() else {
            return Err(syn::Error::new(
                self.span(),
                "`check` argument of `optional` has no value",
            ));
        };
        if !check_tmp.is_empty() {
            return Err(syn::Error::new(
                self.span(),
                "`check` argument of `optional` directive must be a single value",
            ));
        }

        let then_format = self.eval_format(opt.then_format, toplevel)?;
        let else_format = opt
            .else_format
            .map(|f| self.eval_format(f, toplevel))
            .transpose()?;

        Ok(FmtValue::from(Optional {
            check: Box::new(check),
            then_format,
            else_format,
        }))
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
