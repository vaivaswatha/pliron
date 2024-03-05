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

/// Derive the `Printable` trait for IR entities.
pub(crate) fn derive(input: impl Into<TokenStream>) -> Result<TokenStream> {
    let input = syn::parse2::<IRFmtInput>(input.into())?;
    let p = DerivedPrinter::try_from(input)?;
    Ok(p.into_token_stream())
}

/// The derived macro body for the `#[derive(Printable)]` proc macro.
///
/// In pliron operations, attributes, and types are declared and stored differently.
/// Attributes and types are quite similar, as the struct that is used to declare the IR entity
/// also represents its storage.
///
/// This requires a slightly different formatting and evaluation approach for Ops and the other IR
/// entities.
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

/// Representation of the derived `Printable` trait for an attribute or a type IR entity.
///
/// The format string will already be partially evaluated when creating the macro output.
/// See [AttribTypeFmtEvaler] for more details.
///
/// The directives (besides `params` and `struct`) are implemented as macro rules in the
/// pliron::irfmt::printers module.
///
/// Directive macro rules are assumed to have the following signature:
///
/// ```ignore
/// macro_rules! at_name_directive {
///     ($self:ident, ($($printer:ident),*), ($($field_name:tt),*), ($($_param:ident)*)) => {
///     ...
///     }
/// }
/// ```
///
/// The `$printer` argument is the list of arguments normally passed to Printable::fmt.
/// The `$field_name` argument is the list of all field names of the struct.
/// The `$param` argument is the list of all parameters passed to the directive.
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
        let format = evaler.eval(input.format)?;
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

/// Representation of the derived `Printable` trait for an Op IR entity.
///
/// Directives on Ops will be used as is. The directives a completely implemented as macro rules in
/// the pliron::irfmt::printers module.
///
/// Directive macro rules are assumed to have the following signature:
///
/// ```ignore
/// macro_rules! op_name_directive {
///     ( $ctx:ident, $self:ident, $($args:expr),*) => {
///     ...
///     }
/// }
/// ```
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
            format: input.format,
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

/// PrinterBuilder implementations generate a token stream for a derived `Printable` trait.
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

#[cfg(test)]
mod tests {
    use super::*;
    use expect_test::expect;

    fn run_derive(input: TokenStream) -> String {
        let t = derive(input).unwrap();
        let f = syn::parse2::<syn::File>(t).unwrap();
        prettyplease::unparse(&f)
    }

    #[test]
    fn empty_type() {
        let got = run_derive(quote! {
            #[derive(Printable)]
            #[ir_kind = "type"]
            struct EmptyType;
        });

        expect![[r##"
            impl ::pliron::printable::Printable for EmptyType {
                fn fmt(
                    &self,
                    ctx: &::pliron::context::Context,
                    state: &::pliron::printable::State,
                    fmt: &mut ::std::fmt::Formatter<'_>,
                ) -> ::std::fmt::Result {
                    Ok(())
                }
            }
        "##]]
        .assert_eq(&got);
    }

    #[test]
    fn type_with_fields() {
        let got = run_derive(quote! {
            #[derive(Printable)]
            #[ir_kind = "type"]
            struct TypeWithFields {
                field1: u32,
                field2: String,
            }
        });

        expect![[r##"
            impl ::pliron::printable::Printable for TypeWithFields {
                fn fmt(
                    &self,
                    ctx: &::pliron::context::Context,
                    state: &::pliron::printable::State,
                    fmt: &mut ::std::fmt::Formatter<'_>,
                ) -> ::std::fmt::Result {
                    ::pliron::irfmt::printers::literal("<").fmt(ctx, state, fmt)?;
                    ::pliron::irfmt::printers::literal("field1=").fmt(ctx, state, fmt)?;
                    ::pliron::irfmt::printers::print_var!(& self.field1).fmt(ctx, state, fmt)?;
                    ::pliron::irfmt::printers::literal(", ").fmt(ctx, state, fmt)?;
                    ::pliron::irfmt::printers::literal("field2=").fmt(ctx, state, fmt)?;
                    ::pliron::irfmt::printers::print_var!(& self.field2).fmt(ctx, state, fmt)?;
                    ::pliron::irfmt::printers::literal(">").fmt(ctx, state, fmt)?;
                    Ok(())
                }
            }
        "##]]
        .assert_eq(&got);
    }

    #[test]
    fn type_with_format() {
        let got = run_derive(quote! {
            #[derive(Printable)]
            #[ir_kind = "type"]
            #[ir_format = "`value=` $field1"]
            struct TypeWithFormat {
                field1: u32,
                hidden: String,
            }
        });

        expect![[r##"
            impl ::pliron::printable::Printable for TypeWithFormat {
                fn fmt(
                    &self,
                    ctx: &::pliron::context::Context,
                    state: &::pliron::printable::State,
                    fmt: &mut ::std::fmt::Formatter<'_>,
                ) -> ::std::fmt::Result {
                    ::pliron::irfmt::printers::literal("value=").fmt(ctx, state, fmt)?;
                    ::pliron::irfmt::printers::print_var!(& self.field1).fmt(ctx, state, fmt)?;
                    Ok(())
                }
            }
        "##]]
        .assert_eq(&got);
    }

    #[test]
    fn attrib_with_struct_params() {
        let got = run_derive(quote! {
            #[derive(Printable)]
            #[ir_kind = "attribute"]
            #[ir_format = "struct(params)"]
            struct TypeWithFormat {
                a: u32,
                b: String,
            }
        });

        expect![[r##"
            impl ::pliron::printable::Printable for TypeWithFormat {
                fn fmt(
                    &self,
                    ctx: &::pliron::context::Context,
                    state: &::pliron::printable::State,
                    fmt: &mut ::std::fmt::Formatter<'_>,
                ) -> ::std::fmt::Result {
                    ::pliron::irfmt::printers::at_struct_directive!(
                        self, (ctx, state, fmt), (a, b), (a b)
                    );
                    Ok(())
                }
            }
        "##]]
        .assert_eq(&got);
    }

    #[test]
    fn simple_op() {
        let got = run_derive(quote! {
            #[derive(Printable)]
            #[ir_kind = "op"]
            struct SimpleOp;
        });

        expect![[r##"
            impl ::pliron::printable::Printable for SimpleOp {
                fn fmt(
                    &self,
                    ctx: &::pliron::context::Context,
                    state: &::pliron::printable::State,
                    fmt: &mut ::std::fmt::Formatter<'_>,
                ) -> ::std::fmt::Result {
                    if ::pliron::irfmt::printers::op_check_directive!(
                        ctx, self, ::pliron::irfmt::printers::op_results_directive!(ctx, self)
                    ) {
                        ::pliron::irfmt::printers::op_results_directive!(ctx, self)
                            .fmt(ctx, state, fmt)?;
                        ::pliron::irfmt::printers::literal(" = ").fmt(ctx, state, fmt)?;
                    }
                    ::pliron::irfmt::printers::op_operation_generic_format_directive!(ctx, self)
                        .fmt(ctx, state, fmt)?;
                    Ok(())
                }
            }
        "##]]
        .assert_eq(&got);
    }
}
