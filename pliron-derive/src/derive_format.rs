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

#[derive(PartialEq, Eq)]
pub(crate) enum DeriveIRObject {
    Op,
    Attribute,
    Type,
    AnyOtherRustType,
}

/// Derive the [Printable](::pliron::printable::Printable) and
/// [Parsable](::pliron::parsable::Parsable) traits for Rust types.
pub(crate) fn derive(
    args: impl Into<TokenStream>,
    input: impl Into<TokenStream>,
    irobj: DeriveIRObject,
) -> Result<TokenStream> {
    // Parse the input to this macro.
    let input = syn::parse2::<DeriveInput>(input.into())?;

    // Prepare the format description.
    let args = Into::<TokenStream>::into(args);
    let format = if !args.is_empty() {
        let format_str = syn::parse2::<LitStr>(args)?;
        Format::parse(&format_str.value()).map_err(|e| syn::Error::new_spanned(format_str, e))?
    } else if irobj == DeriveIRObject::Op {
        canonical_op_format()
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

    let mut derived = derive_from_parsed(format_input, irobj)?;

    // We're not in a derive macro (but an attribute macro),
    // so attach the original input back.
    derived.extend(input.into_token_stream());
    Ok(derived)
}

/// Derive a token stream for [Printable](::pliron::printable::Printable)
/// and [Parsable](::pliron::parsable::Parsable) traits from [FmtInput].
fn derive_from_parsed(input: FmtInput, irobj: DeriveIRObject) -> Result<TokenStream> {
    let mut format_tokens = TokenStream::new();

    let (printable, parsable) = match irobj {
        DeriveIRObject::Op => (
            DeriveOpPrintable::build(&input)?,
            DeriveOpParsable::build(&input)?,
        ),
        DeriveIRObject::AnyOtherRustType => (
            DeriveBasePrintable::build(&input)?,
            DeriveBaseParsable::build(&input)?,
        ),
        DeriveIRObject::Attribute => (
            DeriveBasePrintable::build(&input)?,
            DeriveAttributeParsable::build(&input)?,
        ),
        DeriveIRObject::Type => (
            DeriveBasePrintable::build(&input)?,
            DeriveTypeParsable::build(&input)?,
        ),
    };

    format_tokens.extend(printable);
    format_tokens.extend(parsable);
    Ok(format_tokens)
}

/// Generate token stream for derived [Printable](::pliron::printable::Printable) trait.
trait PrintableBuilder {
    // Entry function. Builds the outer function outline.
    fn build(input: &FmtInput) -> Result<TokenStream> {
        let name = input.ident.clone();
        let body = Self::build_body(input)?;

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

    // Build the body of the outer function Printable::fmt.
    fn build_body(input: &FmtInput) -> Result<TokenStream> {
        Self::build_format(input)
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

struct DeriveBasePrintable;

impl PrintableBuilder for DeriveBasePrintable {
    fn build_var(input: &FmtInput, name: &str) -> Result<TokenStream> {
        let FmtData::Struct(ref struct_fields) = input.data;
        if !struct_fields
            .fields
            .iter()
            .map(|f| &f.ident)
            .any(|i| i == &FieldIdent::Named(name.to_string()))
        {
            return Err(syn::Error::new_spanned(
                input.ident.clone(),
                format!("field name \"{}\" is invalid", name),
            ));
        }
        let field = format_ident!("{}", name);
        Ok(quote! { ::pliron::printable::Printable::fmt(&self.#field, ctx, state, fmt)?; })
    }

    fn build_unnamed_var(input: &FmtInput, index: usize) -> Result<TokenStream> {
        // This is a struct unnamed field access.
        let FmtData::Struct(ref struct_fields) = input.data;
        if !struct_fields
            .fields
            .iter()
            .map(|f| &f.ident)
            .any(|i| i == &FieldIdent::Unnamed(index))
        {
            return Err(syn::Error::new_spanned(
                input.ident.clone(),
                format!("field index \"{}\" is invalid", index),
            ));
        }
        let index = syn::Index::from(index);
        Ok(quote! { ::pliron::printable::Printable::fmt(&self.#index, ctx, state, fmt)?; })
    }

    fn build_directive(_input: &FmtInput, _d: &Directive) -> Result<TokenStream> {
        todo!()
    }
}

struct DeriveOpPrintable;

impl PrintableBuilder for DeriveOpPrintable {
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
            Ok(quote! { ::pliron::op::canonical_syntax_print(Box::new(*self), ctx, state, f) })
        } else {
            todo!()
        }
    }

    fn build_body(_input: &FmtInput) -> Result<TokenStream> {
        todo!()
    }
}

/// Generate token stream for derived [Printable](::pliron::printable::Printable) trait.
trait ParsableBuilder {
    /// Entry point to build a parser.
    fn build(input: &FmtInput) -> Result<TokenStream> {
        let name = input.ident.clone();
        let body = Self::build_body(input)?;
        let final_ret_value = Self::build_final_ret_value();

        let arg = Self::build_assoc_type_arg()?;
        let parsed = Self::build_assoc_type_parsed()?;
        let derived = quote! {
            impl ::pliron::parsable::Parsable for #name {
                type Arg = #arg;
                type Parsed = #parsed;
                fn parse<'a>(
                    state_stream: &mut ::pliron::parsable::StateStream<'a>,
                    results: Self::Arg,
                ) -> ::pliron::parsable::ParseResult<'a, Self::Parsed> {
                    use ::pliron::parsable::IntoParseResult;
                    use ::combine::Parser;
                    #body
                    #final_ret_value
                }
            }
        };
        Ok(derived)
    }

    /// Default implementation for building the parser's associated type for `Arg`.
    fn build_assoc_type_arg() -> Result<TokenStream> {
        Ok(quote! { () })
    }

    /// Default implementation for building the parser's associated type for `Parsed`.
    fn build_assoc_type_parsed() -> Result<TokenStream> {
        Ok(quote! { Self })
    }

    fn build_lit(lit: &str) -> TokenStream {
        quote! {
            ::pliron::irfmt::parsers::spaced(::combine::parser::char::string(#lit))
            .parse_stream(state_stream)
            .into_result()?;
        }
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

    fn build_body(input: &FmtInput) -> Result<TokenStream> {
        let mut processed_fmt = Self::build_format(input)?;
        let FmtData::Struct(r#struct) = &input.data;
        let name = &r#struct.name;
        let mut named = true;

        let mut obj_builder = quote! {};
        for field in &r#struct.fields {
            match &field.ident {
                FieldIdent::Named(name) => {
                    let field_name = format_ident!("{}", name);
                    obj_builder.extend(quote! {
                        #field_name,
                    });
                }
                FieldIdent::Unnamed(index) => {
                    let field_name = format_ident!("field_at_{}", index);
                    obj_builder.extend(quote! {
                        #field_name,
                    });
                    named = false;
                }
            }
        }

        let final_ret_value = if named {
            quote! {
                let final_ret_value = #name {
                    #obj_builder
                };
            }
        } else {
            quote! {
                let final_ret_value = #name (
                    #obj_builder
                );
            }
        };

        processed_fmt.extend(quote! {
            #final_ret_value
        });
        Ok(processed_fmt)
    }

    fn build_var(input: &FmtInput, name: &str) -> Result<TokenStream> {
        let FmtData::Struct(r#struct) = &input.data;

        let Some(crate::irfmt::Field { ty, .. }) = r#struct
            .fields
            .iter()
            .find(|f| matches!(&f.ident, FieldIdent::Named(field_name) if name == field_name))
        else {
            return Err(syn::Error::new_spanned(
                input.ident.clone(),
                format!("{} field not found", name),
            ));
        };
        let name = format_ident!("{}", name);
        Ok(quote! {
            let #name = <#ty>::parser(()).parse_stream(state_stream).into_result()?.0;
        })
    }

    fn build_unnamed_var(input: &FmtInput, index: usize) -> Result<TokenStream> {
        let FmtData::Struct(r#struct) = &input.data;
        let crate::irfmt::Field { ty, .. } =
            r#struct.fields.get(index).ok_or(syn::Error::new_spanned(
                input.ident.clone(),
                format!("field index \"{}\" is invalid", index),
            ))?;
        let name = format_ident!("field_at_{}", index);
        Ok(quote! {
            let #name = <#ty>::parser(()).parse_stream(state_stream).into_result()?.0;
        })
    }

    fn build_directive(_input: &FmtInput, _d: &Directive) -> Result<TokenStream> {
        unimplemented!("No directives supported in default trait implementation")
    }

    /// After the entire body is built, build the parsed value to be finally returned.
    fn build_final_ret_value() -> TokenStream {
        quote! {
            Ok(final_ret_value).into_parse_result()
        }
    }
}

/// Basic parsable builder for any Rust type.
/// Builds an object of that type.
/// Requires all contents to be parsable themselves.
struct DeriveBaseParsable;

impl ParsableBuilder for DeriveBaseParsable {
    fn build_directive(_input: &FmtInput, _d: &Directive) -> Result<TokenStream> {
        todo!()
    }
}

struct DeriveOpParsable;

impl ParsableBuilder for DeriveOpParsable {
    fn build_body(_input: &FmtInput) -> Result<TokenStream> {
        todo!()
    }

    fn build_var(_input: &FmtInput, _name: &str) -> Result<TokenStream> {
        todo!()
    }

    fn build_unnamed_var(_input: &FmtInput, _index: usize) -> Result<TokenStream> {
        todo!()
    }

    fn build_directive(_input: &FmtInput, _d: &Directive) -> Result<TokenStream> {
        todo!()
    }

    fn build_final_ret_value() -> TokenStream {
        todo!()
    }
}

struct DeriveAttributeParsable;

impl ParsableBuilder for DeriveAttributeParsable {
    fn build_directive(_input: &FmtInput, _d: &Directive) -> Result<TokenStream> {
        todo!()
    }
}

struct DeriveTypeParsable;

impl ParsableBuilder for DeriveTypeParsable {
    fn build_directive(_input: &FmtInput, _d: &Directive) -> Result<TokenStream> {
        todo!()
    }

    fn build_assoc_type_parsed() -> Result<TokenStream> {
        Ok(quote! { ::pliron::r#type::TypePtr<Self> })
    }

    fn build_final_ret_value() -> TokenStream {
        quote! {
            Ok(::pliron::r#type::Type::register_instance(final_ret_value, state_stream.state.ctx)).into_parse_result()
        }
    }
}
