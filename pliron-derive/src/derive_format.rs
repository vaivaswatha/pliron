use proc_macro2::TokenStream;
use quote::{format_ident, quote, ToTokens};
use syn::{DeriveInput, LitStr, Result};

use crate::irfmt::{
    canonical_format_for_structs, canonical_op_format, Directive, Elem, FieldIdent, FmtData,
    Format, Lit, UnnamedVar, Var,
};

/// Data parsed from the macro to derive formatting for Rust types
pub(crate) struct FmtInput {
    pub ident: syn::Ident,
    pub data: FmtData,
    pub format: Format,
}

/// Derive the [Printable](::pliron::printable::Printable) and
/// [Parsable](::pliron::parsable::Parsable) traits for Rust types.
pub(crate) fn derive(
    args: impl Into<TokenStream>,
    input: impl Into<TokenStream>,
) -> Result<TokenStream> {
    // Parse the input to this macro.
    let input = syn::parse2::<DeriveInput>(input.into())?;

    // Prepare the format description.
    let args = Into::<TokenStream>::into(args);
    let format = if !args.is_empty() {
        let format_str = syn::parse2::<LitStr>(args)?;
        Format::parse(&format_str.value()).map_err(|e| syn::Error::new_spanned(format_str, e))?
    } else {
        canonical_format_for_structs(&input)?
    };

    // Prepare data for the deriver.
    let format_data = FmtData::try_from(input.clone())?;
    let format_input = FmtInput {
        ident: input.ident.clone(),
        data: format_data,
        format,
    };

    let mut derived = derive_from_parsed(format_input)?;

    // We're not in a derive macro (but an attribute macro),
    // so attach the original input back.
    derived.extend(input.into_token_stream());
    Ok(derived)
}

/// Derive a token stream for [Printable](::pliron::printable::Printable)
/// and [Parsable](::pliron::parsable::Parsable) traits from [FmtInput].
fn derive_from_parsed(input: FmtInput) -> Result<TokenStream> {
    let mut format_tokens = TokenStream::new();
    let printable = DerivePrintable::build(&input)?;
    let parsable = TokenStream::new(); // DeriveParsable::build(&input)?;

    format_tokens.extend(printable);
    format_tokens.extend(parsable);
    Ok(format_tokens)
}

/// Generate token stream for derived [Printable](::pliron::printable::Printable) trait.
trait PrintableBuilder {
    fn build(input: &FmtInput) -> Result<TokenStream> {
        let name = input.ident.clone();
        let body = Self::build_format(input)?;

        let derived = quote! {
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
        };
        Ok(derived)
    }

    fn build_lit(lit: &str) -> TokenStream {
        quote! { ::pliron::printable::Printable::fmt(&#lit, ctx, state, fmt)?; }
    }

    fn build_format(input: &FmtInput) -> Result<TokenStream> {
        let derived_format = input
            .format
            .elems
            .iter()
            .map(|elem| Self::build_elem(input, elem))
            .try_fold(TokenStream::new(), |mut acc, e| {
                acc.extend(e?);
                Ok(acc)
            });
        derived_format
    }

    fn build_elem(input: &FmtInput, elem: &Elem) -> Result<TokenStream> {
        match elem {
            Elem::Lit(Lit { lit, .. }) => Ok(Self::build_lit(lit)),
            Elem::Var(Var { name, .. }) => Self::build_var(input, name),
            Elem::UnnamedVar(UnnamedVar { index, .. }) => Self::build_unnamed_var(input, *index),
            Elem::Directive(ref d) => Self::build_directive(input, d),
        }
    }

    fn build_var(input: &FmtInput, name: &str) -> Result<TokenStream>;
    fn build_unnamed_var(input: &FmtInput, index: usize) -> Result<TokenStream>;
    fn build_directive(input: &FmtInput, d: &Directive) -> Result<TokenStream>;
}

struct DerivePrintable;

impl PrintableBuilder for DerivePrintable {
    fn build_var(input: &FmtInput, name: &str) -> Result<TokenStream> {
        let FmtData::Struct(ref struct_fields) = input.data;
        if !struct_fields
            .fields
            .contains(&FieldIdent::Named(name.to_string()))
        {
            return Err(syn::Error::new_spanned(
                input.ident.clone(),
                format!("{} field name mismatch", name),
            ));
        }
        let field = format_ident!("{}", name);
        Ok(quote! { ::pliron::printable::Printable::fmt(&self.#field, ctx, state, fmt)?; })
    }

    fn build_unnamed_var(input: &FmtInput, index: usize) -> Result<TokenStream> {
        // This is a struct unnamed field access.
        let FmtData::Struct(ref struct_fields) = input.data;
        if !struct_fields.fields.contains(&FieldIdent::Unnamed(index)) {
            return Err(syn::Error::new_spanned(
                input.ident.clone(),
                format!("{} field index mismatch", index),
            ));
        }
        let index = syn::Index::from(index);
        Ok(quote! { ::pliron::printable::Printable::fmt(&self.#index, ctx, state, fmt)?; })
    }

    fn build_directive(_input: &FmtInput, _d: &Directive) -> Result<TokenStream> {
        todo!()
    }
}

/// Derive the [Printable](::pliron::printable::Printable)
/// and [Parsable](::pliron::parsable::Parsable) traits for
/// [Op](../pliron/op/trait.Op.html)s
pub(crate) fn op_derive(
    args: impl Into<TokenStream>,
    input: impl Into<TokenStream>,
) -> Result<TokenStream> {
    // Parse the input to this macro.
    let input = syn::parse2::<DeriveInput>(input.into())?;

    // Prepare the format description.
    let args = Into::<TokenStream>::into(args);
    let format = if !args.is_empty() {
        let format_str = syn::parse2::<LitStr>(args)?;
        Format::parse(&format_str.value()).map_err(|e| syn::Error::new_spanned(format_str, e))?
    } else {
        canonical_op_format()
    };

    // Prepare data for the deriver.
    let format_data = FmtData::try_from(input.clone())?;
    let format_input = FmtInput {
        ident: input.ident.clone(),
        data: format_data,
        format,
    };

    let mut derived = op_derive_from_parsed(format_input)?;

    // We're not in a derive macro (but an attribute macro),
    // so attach the original input back.
    derived.extend(input.into_token_stream());
    Ok(derived)
}

/// Derive a token stream for `Printable` and `Parsable` from [OpFmtInput].
fn op_derive_from_parsed(input: FmtInput) -> Result<TokenStream> {
    let mut format_tokens = TokenStream::new();
    let printable = OpDerivePrintable::build(&input)?;
    let parsable = TokenStream::new(); // DeriveParsable::build(&input)?;

    format_tokens.extend(printable);
    format_tokens.extend(parsable);
    Ok(format_tokens)
}

struct OpDerivePrintable;

impl PrintableBuilder for OpDerivePrintable {
    fn build_var(input: &FmtInput, name: &str) -> Result<TokenStream> {
        let op_name = input.ident.clone();
        let attr_name = format_ident!("{}", name);
        Ok(quote! {
            let attr = self
                .get_operation(ctx)
                .attributes.0.get(#attr_name)
                .expect("Missing attribute {} on Op {}", name, #op_name);
            ::pliron::printable::Printable::fmt(attr, ctx, state, fmt)?;
        })
    }

    fn build_unnamed_var(_input: &FmtInput, index: usize) -> Result<TokenStream> {
        Ok(quote! {
            let opd = self.get_operation().deref(ctx).get_operand(#index);
            ::pliron::printable::Printable::fmt(&opd, ctx, state, fmt)?;
        })
    }

    fn build_directive(_input: &FmtInput, d: &Directive) -> Result<TokenStream> {
        if d.name == "canonical" {
            Ok(quote! { ::pliron::op::canonical_syntax_fmt(Box::new(*self), ctx, state, f) })
        } else {
            todo!()
        }
    }
}
