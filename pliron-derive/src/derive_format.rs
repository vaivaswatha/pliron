use proc_macro2::TokenStream;
use quote::{format_ident, quote, ToTokens};
use rustc_hash::FxHashMap;
use syn::{spanned::Spanned, Data, DeriveInput, LitStr, Result};

use crate::irfmt::{
    canonical_format_for_enums, canonical_format_for_structs, canonical_op_format, Directive, Elem,
    FieldIdent, FmtData, Format, Lit, UnnamedVar, Var,
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

/// enums can have a `#[format]` for its variants.
/// Those shouldn't be in the final output, so we remove them.
fn erase_helper_attributes(mut input: DeriveInput) -> DeriveInput {
    match input.data {
        Data::Struct(_) | Data::Union(_) => input,
        Data::Enum(ref mut data) => {
            for variant in &mut data.variants {
                variant.attrs.clear();
            }
            input
        }
    }
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
    let format_data = FmtData::try_from(input.clone())?;

    let format = if let FmtData::Enum(_) = format_data {
        // Enums have only one preset format and are not customizable.
        if !args.is_empty() {
            return Err(syn::Error::new_spanned(
                input,
                "Custom format strings for enums can only be specified for individual variants"
                    .to_string(),
            ));
        }
        canonical_format_for_enums()
    } else if !args.is_empty() {
        let format_str = syn::parse2::<LitStr>(args)?;
        Format::parse(&format_str.value()).map_err(|e| syn::Error::new_spanned(format_str, e))?
    } else if irobj == DeriveIRObject::Op {
        canonical_op_format()
    } else {
        canonical_format_for_structs(&format_data, input.span())?
    };

    // Prepare data for the deriver.
    let format_input = FmtInput {
        ident: input.ident.clone(),
        data: format_data,
        format,
    };

    let mut derived = derive_from_parsed(format_input, irobj)?;

    // We're not in a derive macro (but an attribute macro),
    // so attach the original input back.
    derived.extend(erase_helper_attributes(input).into_token_stream());
    Ok(derived)
}

/// Derive a token stream for [Printable](::pliron::printable::Printable)
/// and [Parsable](::pliron::parsable::Parsable) traits from [FmtInput].
fn derive_from_parsed(input: FmtInput, irobj: DeriveIRObject) -> Result<TokenStream> {
    let mut format_tokens = TokenStream::new();

    let (printable, parsable) = match irobj {
        DeriveIRObject::Op => (
            DeriveOpPrintable::build(&input)?,
            DeriveOpParsable::build(&input, &mut OpParserState::default())?,
        ),
        DeriveIRObject::AnyOtherRustType => (
            DeriveBasePrintable::build(&input)?,
            DeriveBaseParsable::build(&input, &mut ())?,
        ),
        DeriveIRObject::Attribute => (
            DeriveBasePrintable::build(&input)?,
            DeriveAttributeParsable::build(&input, &mut ())?,
        ),
        DeriveIRObject::Type => (
            DeriveBasePrintable::build(&input)?,
            DeriveTypeParsable::build(&input, &mut ())?,
        ),
    };

    format_tokens.extend(printable);
    format_tokens.extend(parsable);
    Ok(format_tokens)
}

#[derive(Default)]
struct OpPrinterState {
    is_canonical: bool,
}

/// Generate token stream for derived [Printable](::pliron::printable::Printable) trait.
trait PrintableBuilder<State: Default> {
    // Entry function. Builds the outer function outline.
    fn build(input: &FmtInput) -> Result<TokenStream> {
        let name = input.ident.clone();
        let body = Self::build_body(input, &mut State::default())?;

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
    fn build_body(input: &FmtInput, state: &mut State) -> Result<TokenStream> {
        if let FmtData::Enum(r#enum) = &input.data {
            let mut output = quote! {};
            for (format, r#struct) in &r#enum.variants {
                let variant_name = r#struct.name.clone();
                let variant_input = FmtInput {
                    ident: variant_name.clone(),
                    data: FmtData::Struct(r#struct.clone()),
                    format: format.clone(),
                };
                let mut variant_fields = quote! {};
                if !r#struct.fields.is_empty() {
                    let mut is_named = false;
                    let mut fields = quote! {};
                    for field in &r#struct.fields {
                        let field_name = field.ident.clone();
                        match field_name {
                            FieldIdent::Named(name) => {
                                is_named = true;
                                let field = format_ident!("{}", name);
                                fields.extend(quote! {
                                    #field,
                                });
                            }
                            FieldIdent::Unnamed(index) => {
                                let field = format_ident!("field_at_{}", index);
                                fields.extend(quote! {
                                    #field,
                                });
                            }
                        }
                    }
                    if is_named {
                        variant_fields.extend(quote! {
                            { #fields }
                        });
                    } else {
                        variant_fields.extend(quote! {
                            ( #fields )
                        });
                    }
                }
                let variant_tokens = Self::build_format(&variant_input, state)?;
                output.extend(quote! {
                    Self::#variant_name #variant_fields => {
                        write!(fmt, "{}", stringify!(#variant_name))?;
                        #variant_tokens
                    },
                });
            }
            Ok(quote! {
                match self {
                    #output
                }
            })
        } else {
            Self::build_format(input, state)
        }
    }

    fn build_lit(_input: &FmtInput, _state: &mut State, lit: &str) -> TokenStream {
        quote! { ::pliron::printable::Printable::fmt(&#lit, ctx, state, fmt)?; }
    }

    fn build_format(input: &FmtInput, state: &mut State) -> Result<TokenStream> {
        let derived_format = input
            .format
            .elems
            .iter()
            .map(|elem| Self::build_elem(input, state, elem))
            .try_fold(TokenStream::new(), |mut acc, e| {
                acc.extend(e?);
                Ok(acc)
            });
        derived_format
    }

    fn build_elem(input: &FmtInput, state: &mut State, elem: &Elem) -> Result<TokenStream> {
        match elem {
            Elem::Lit(Lit { lit, .. }) => Ok(Self::build_lit(input, state, lit)),
            Elem::Var(Var { name, .. }) => Self::build_var(input, state, name),
            Elem::UnnamedVar(UnnamedVar { index, .. }) => {
                Self::build_unnamed_var(input, state, *index)
            }
            Elem::Directive(ref d) => Self::build_directive(input, state, d),
        }
    }

    fn build_var(input: &FmtInput, state: &mut State, name: &str) -> Result<TokenStream>;
    fn build_unnamed_var(input: &FmtInput, state: &mut State, index: usize) -> Result<TokenStream>;
    fn build_directive(input: &FmtInput, state: &mut State, d: &Directive) -> Result<TokenStream>;
}

struct DeriveBasePrintable;

impl PrintableBuilder<()> for DeriveBasePrintable {
    fn build_var(input: &FmtInput, _state: &mut (), name: &str) -> Result<TokenStream> {
        let FmtData::Struct(ref r#struct) = input.data else {
            return Err(syn::Error::new_spanned(
                input.ident.clone(),
                "Only structs fields as variables are supported".to_string(),
            ));
        };
        if !r#struct
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
        let field_name = format_ident!("{}", name);
        // If the field is an enum variant, then we don't need to access it with `&self`.
        let field = if r#struct.is_enum_variant {
            quote! { #field_name }
        } else {
            quote! { &self.#field_name }
        };
        Ok(quote! { ::pliron::printable::Printable::fmt(#field, ctx, state, fmt)?; })
    }

    fn build_unnamed_var(input: &FmtInput, _state: &mut (), index: usize) -> Result<TokenStream> {
        // This is a struct unnamed field access.
        let FmtData::Struct(ref r#struct) = input.data else {
            return Err(syn::Error::new_spanned(
                input.ident.clone(),
                "Only tuple indices in structs (tuples) are supported".to_string(),
            ));
        };
        if !r#struct
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
        // If the field is an enum variant, then we don't need to access it with `&self`,
        // but instead need to use the index field which we gave a name to, when expanding
        // the match arm.
        let field = if r#struct.is_enum_variant {
            let field_at_index = format_ident!("field_at_{}", index);
            quote! { #field_at_index }
        } else {
            quote! { &self.#index }
        };
        Ok(quote! { ::pliron::printable::Printable::fmt(#field, ctx, state, fmt)?; })
    }

    fn build_directive(_input: &FmtInput, _state: &mut (), _d: &Directive) -> Result<TokenStream> {
        unimplemented!("No directives supported in DeriveBasePrintable")
    }
}

struct DeriveOpPrintable;

impl PrintableBuilder<OpPrinterState> for DeriveOpPrintable {
    fn build_var(
        input: &FmtInput,
        _state: &mut OpPrinterState,
        attr_name: &str,
    ) -> Result<TokenStream> {
        let attr_name = attr_name.to_string();
        let op_name = input.ident.clone();
        let missing_attr_err = format!("Missing attribute {} on Op {}", &attr_name, &op_name);
        Ok(quote! {
            {
                let name = #attr_name.try_into().expect("Invalid attribute name");
                let self_op = self.get_operation().deref(ctx);
                let attr = self_op.attributes.0.get(&name).expect(&#missing_attr_err);
                ::pliron::printable::Printable::fmt(attr, ctx, state, fmt)?;
            }
        })
    }

    fn build_unnamed_var(
        _input: &FmtInput,
        _state: &mut OpPrinterState,
        index: usize,
    ) -> Result<TokenStream> {
        Ok(quote! {
            let opd = self.get_operation().deref(ctx).get_operand(#index);
            ::pliron::printable::Printable::fmt(&opd, ctx, state, fmt)?;
        })
    }

    fn build_directive(
        input: &FmtInput,
        state: &mut OpPrinterState,
        d: &Directive,
    ) -> Result<TokenStream> {
        if d.name == "canonical" {
            state.is_canonical = true;
            Ok(quote! { ::pliron::op::canonical_syntax_print(Box::new(*self), ctx, state, fmt)?; })
        } else if d.name == "type" {
            let err = Err(syn::Error::new_spanned(
                    input.ident.clone(),
                    "The `type` directive takes a single unnamed variable argument to specify the result index".to_string(),
                ));
            if d.args.len() != 1 {
                return err;
            }
            if let Elem::UnnamedVar(UnnamedVar { index, .. }) = &d.args[0] {
                Ok(quote! {
                    let res = self.get_operation().deref(ctx).get_type(#index);
                    ::pliron::printable::Printable::fmt(&res, ctx, state, fmt)?;
                })
            } else {
                return err;
            }
        } else if d.name == "region" {
            let err = Err(syn::Error::new_spanned(
                input.ident.clone(),
                "The `region` directive takes a single unnamed variable argument to specify the region index".to_string(),
            ));
            if d.args.len() != 1 {
                return err;
            }
            if let Elem::UnnamedVar(UnnamedVar { index, .. }) = &d.args[0] {
                Ok(quote! {
                    let reg = self.get_operation().deref(ctx).get_region(#index);
                    ::pliron::printable::Printable::fmt(&reg, ctx, state, fmt)?;
                })
            } else {
                return err;
            }
        } else if d.name == "attr" {
            let (attr_name_str, attr_type_path) = parse_attr_directive_args(d, input)?;
            Ok(quote! {
                let self_op = self.get_operation().deref(ctx);
                let attr = self_op.attributes.get::<#attr_type_path>(
                    &::pliron::identifier::Identifier::try_from(#attr_name_str).unwrap()
                ).expect("Missing attribute");
                ::pliron::printable::Printable::fmt(attr, ctx, state, fmt)?;
            })
        } else {
            unimplemented!("Unknown directive {}", d.name)
        }
    }

    fn build_body(input: &FmtInput, state: &mut OpPrinterState) -> Result<TokenStream> {
        let formatted_tokens = Self::build_format(input, state)?;
        let mut output = quote! {};
        if !state.is_canonical {
            output.extend(quote! {
                use ::pliron::op::Op;
                use ::pliron::irfmt::printers::iter_with_sep;
                let op = self.get_operation().deref(ctx);
                if op.get_num_results() > 0 {
                    let sep = ::pliron::printable::ListSeparator::CharSpace(',');
                    let results = iter_with_sep(op.results(), sep);
                    write!(fmt, "{} = ", results.disp(ctx))?;
                }
                write!(fmt, "{} ", self.get_opid())?;
            });
        }
        output.extend(formatted_tokens);
        Ok(output)
    }
}

/// Generate token stream for derived [Printable](::pliron::printable::Printable) trait.
trait ParsableBuilder<State: Default> {
    /// Entry point to build a parser.
    fn build(input: &FmtInput, state: &mut State) -> Result<TokenStream> {
        let name = input.ident.clone();
        let body = Self::build_body(input, state)?;
        let final_ret_value = Self::build_final_ret_value(input, state);

        let arg = Self::build_assoc_type_arg(input, state)?;
        let parsed = Self::build_assoc_type_parsed(input, state)?;
        let derived = quote! {
            impl ::pliron::parsable::Parsable for #name {
                type Arg = #arg;
                type Parsed = #parsed;
                fn parse<'a>(
                    state_stream: &mut ::pliron::parsable::StateStream<'a>,
                    arg: Self::Arg,
                ) -> ::pliron::parsable::ParseResult<'a, Self::Parsed> {
                    use ::pliron::parsable::IntoParseResult;
                    use ::combine::Parser;
                    use ::pliron::input_err;
                    use ::pliron::location::Located;
                    let cur_loc = state_stream.loc();

                    #body
                    #final_ret_value
                }
            }
        };
        Ok(derived)
    }

    /// Default implementation for building the parser's associated type for `Arg`.
    fn build_assoc_type_arg(_input: &FmtInput, _state: &mut State) -> Result<TokenStream> {
        Ok(quote! { () })
    }

    /// Default implementation for building the parser's associated type for `Parsed`.
    fn build_assoc_type_parsed(_input: &FmtInput, _state: &mut State) -> Result<TokenStream> {
        Ok(quote! { Self })
    }

    fn build_lit(_input: &FmtInput, lit: &str, _state: &mut State) -> TokenStream {
        quote! {
            ::pliron::irfmt::parsers::spaced(::combine::parser::char::string(#lit))
            .parse_stream(state_stream)
            .into_result()?;
        }
    }

    fn build_format(input: &FmtInput, state: &mut State) -> Result<TokenStream> {
        let derived_format = input
            .format
            .elems
            .iter()
            .map(|elem| Self::build_elem(input, state, elem))
            .try_fold(TokenStream::new(), |mut acc, e| {
                acc.extend(e?);
                Ok(acc)
            });
        derived_format
    }

    fn build_elem(input: &FmtInput, state: &mut State, elem: &Elem) -> Result<TokenStream> {
        match elem {
            Elem::Lit(Lit { lit, .. }) => Ok(Self::build_lit(input, lit, state)),
            Elem::Var(Var { name, .. }) => Self::build_var(input, state, name),
            Elem::UnnamedVar(UnnamedVar { index, .. }) => {
                Self::build_unnamed_var(input, state, *index)
            }
            Elem::Directive(ref d) => Self::build_directive(input, state, d),
        }
    }

    fn build_body(input: &FmtInput, state: &mut State) -> Result<TokenStream> {
        if let FmtData::Enum(r#enum) = &input.data {
            let enum_name = r#enum.name.clone();
            assert!(!r#enum.variants.is_empty(), "Enum has no variants");
            let variant_name_parsed = quote! {
                let variant_name_parsed =
                    ::pliron::identifier::Identifier::parser(()).
                    parse_stream(state_stream).into_result()?.0.to_string();
            };

            let mut match_arms = quote! {};
            for (format, r#struct) in &r#enum.variants {
                let variant_name = r#struct.name.clone();
                let variant_name_str = variant_name.to_string();
                let parsed_variant = if r#struct.fields.is_empty() {
                    quote! {
                        // Could as well use Self::#variant_name here.
                        #enum_name::#variant_name
                    }
                } else {
                    let variant_input = FmtInput {
                        ident: r#struct.name.clone(),
                        data: FmtData::Struct(r#struct.clone()),
                        format: format.clone(),
                    };
                    let built_body = Self::build_body(&variant_input, state)?;
                    quote! {
                        #built_body
                        final_ret_value
                    }
                };
                match_arms.extend(quote! {
                    #variant_name_str => {
                        #parsed_variant
                    },
                });
            }
            return Ok(quote! {
                #variant_name_parsed
                let final_ret_value = match variant_name_parsed.as_str() {
                    #match_arms
                    _ => {
                        return input_err!(
                            cur_loc,
                            "Invalid variant name: {}", variant_name_parsed
                        )?;
                    }
                };
            });
        }

        let mut processed_fmt = Self::build_format(input, state)?;
        let FmtData::Struct(r#struct) = &input.data else {
            return Err(syn::Error::new_spanned(
                input.ident.clone(),
                "Only structs are supported by default impl of ParsableBuilder".to_string(),
            ));
        };
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

        let name_prefix = if r#struct.is_enum_variant {
            quote! { Self:: }
        } else {
            quote! {}
        };
        let final_ret_value = if named {
            quote! {
                let final_ret_value = #name_prefix #name {
                    #obj_builder
                };
            }
        } else {
            quote! {
                let final_ret_value = #name_prefix #name (
                    #obj_builder
                );
            }
        };

        processed_fmt.extend(quote! {
            #final_ret_value
        });
        Ok(processed_fmt)
    }

    fn build_var(input: &FmtInput, _state: &mut State, name: &str) -> Result<TokenStream> {
        let FmtData::Struct(r#struct) = &input.data else {
            return Err(syn::Error::new_spanned(
                input.ident.clone(),
                "Only structs fields as variables are supported".to_string(),
            ));
        };

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

    fn build_unnamed_var(
        input: &FmtInput,
        _state: &mut State,
        index: usize,
    ) -> Result<TokenStream> {
        let FmtData::Struct(r#struct) = &input.data else {
            return Err(syn::Error::new_spanned(
                input.ident.clone(),
                "Only tuple indices in structs (tuples) are supported".to_string(),
            ));
        };

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

    fn build_directive(
        _input: &FmtInput,
        _state: &mut State,
        _d: &Directive,
    ) -> Result<TokenStream> {
        unimplemented!("No directives supported in default trait implementation")
    }

    /// After the entire body is built, build the parsed value to be finally returned.
    fn build_final_ret_value(_input: &FmtInput, _state: &mut State) -> TokenStream {
        quote! {
            Ok(final_ret_value).into_parse_result()
        }
    }
}

/// Basic parsable builder for any Rust type.
/// Builds an object of that type.
/// Requires all contents to be parsable themselves.
struct DeriveBaseParsable;

impl ParsableBuilder<()> for DeriveBaseParsable {
    fn build_directive(_input: &FmtInput, _state: &mut (), _d: &Directive) -> Result<TokenStream> {
        unimplemented!("No directives supported in DeriveBaseParsable")
    }
}

#[derive(Default)]
struct OpParserState {
    is_canonical: bool,
    operands: FxHashMap<usize, syn::Ident>,
    result_types: FxHashMap<usize, syn::Ident>,
    attributes: FxHashMap<String, syn::Ident>,
    regions: FxHashMap<usize, syn::Ident>,
}

struct DeriveOpParsable;

impl ParsableBuilder<OpParserState> for DeriveOpParsable {
    fn build_body(input: &FmtInput, state: &mut OpParserState) -> Result<TokenStream> {
        let mut output = quote! {
            use ::pliron::op::Op;
            use ::pliron::operation::Operation;
            use ::pliron::irfmt::parsers::{process_parsed_ssa_defs, ssa_opd_parser, attr_parser};
        };

        let built_format = Self::build_format(input, state)?;
        output.extend(built_format);

        if state.is_canonical {
            return Ok(output);
        }

        let num_operands = state
            .operands
            .keys()
            .map(|idx| idx + 1)
            .max()
            .unwrap_or_default();
        let num_result_types = state
            .result_types
            .keys()
            .map(|idx| idx + 1)
            .max()
            .unwrap_or_default();
        let num_regions = state
            .regions
            .keys()
            .map(|idx| idx + 1)
            .max()
            .unwrap_or_default();

        for i in 0..num_operands {
            if !state.operands.contains_key(&i) {
                return Err(syn::Error::new_spanned(
                    input.ident.clone(),
                    format!("missing operand {}", i),
                ));
            }
        }

        for i in 0..num_result_types {
            if !state.result_types.contains_key(&i) {
                return Err(syn::Error::new_spanned(
                    input.ident.clone(),
                    format!("missing type for result {}", i),
                ));
            }
        }

        let results_check = quote! {
            if arg.len() != #num_result_types {
                return
                    input_err!(cur_loc,
                        "expected {} results as per spec, got {} during parsing",
                        #num_result_types,
                        arg.len()
                    )?;
            }
        };

        for i in 0..num_regions {
            if !state.regions.contains_key(&i) {
                return Err(syn::Error::new_spanned(
                    input.ident.clone(),
                    format!("missing region {}", i),
                ));
            }
        }

        output.extend(results_check);

        let operand_indices = (0..num_operands).map(|i| state.operands[&i].clone());
        let operands = quote! {
            vec![#( #operand_indices ),*]
        };
        let result_indices = (0..num_result_types).map(|i| state.result_types[&i].clone());
        let results = quote! {
            vec![#( #result_indices ),*]
        };
        let region_indices = (0..num_regions).map(|i| state.regions[&i].clone());
        let regions = quote! {
            vec![#( #region_indices ),*]
        };
        let mut attribute_sets = quote! {};
        for (attr_name, attr_ident) in &state.attributes {
            attribute_sets.extend(quote! {
                op.deref_mut(state_stream.state.ctx).attributes.0.insert(
                    ::pliron::identifier::Identifier::try_from(#attr_name).unwrap(),
                    #attr_ident,
                );
            });
        }

        output.extend(quote! {
            let op = ::pliron::operation::Operation::new(
                state_stream.state.ctx,
                Self::get_opid_static(),
                #results,
                #operands,
                vec![],   // successors
                0,        // regions
            );
            for region in #regions {
                ::pliron::region::Region::move_to_op(region, op, state_stream.state.ctx);
            }
            process_parsed_ssa_defs(state_stream, &arg, op)?;
            let final_ret_value = Operation::get_op(op, state_stream.state.ctx);
        });

        output.extend(attribute_sets);

        Ok(output)
    }

    fn build_var(
        _input: &FmtInput,
        state: &mut OpParserState,
        attr_name: &str,
    ) -> Result<TokenStream> {
        let attr_name = attr_name.to_string();
        let attr_name_ident = format_ident!("{}", attr_name);
        state
            .attributes
            .insert(attr_name.clone(), attr_name_ident.clone());
        Ok(quote! {
            let #attr_name_ident = attr_parser()
                .parse_stream(state_stream)
                .into_result()?
                .0;
        })
    }

    fn build_unnamed_var(
        _input: &FmtInput,
        state: &mut OpParserState,
        index: usize,
    ) -> Result<TokenStream> {
        let opd_name = format_ident!("opd_{}", index);
        state.operands.insert(index, opd_name.clone());
        Ok(quote! {
            let #opd_name = ssa_opd_parser().parse_stream(state_stream).into_result()?.0;
        })
    }

    fn build_directive(
        input: &FmtInput,
        state: &mut OpParserState,
        d: &Directive,
    ) -> Result<TokenStream> {
        if d.name == "canonical" {
            state.is_canonical = true;
            Ok(quote! {
                ::pliron::op::canonical_syntax_parser(
                    <Self as ::pliron::op::Op>::get_opid_static(),
                    arg,
                )
                .parse_stream(state_stream)
                .into()
            })
        } else if d.name == "type" {
            let err = Err(syn::Error::new_spanned(
                    input.ident.clone(),
                    "The `type` directive takes a single unnamed variable argument to specify the result index".to_string(),
                ));
            if d.args.len() != 1 {
                return err;
            }
            if let Elem::UnnamedVar(UnnamedVar { index, .. }) = &d.args[0] {
                let res_type = format_ident!("res_{}", index);
                state.result_types.insert(*index, res_type.clone());
                Ok(quote! {
                    let #res_type = ::pliron::irfmt::parsers::type_parser().parse_stream(state_stream).into_result()?.0;
                })
            } else {
                return err;
            }
        } else if d.name == "region" {
            let err = Err(syn::Error::new_spanned(
                input.ident.clone(),
                "The `region` directive takes a single unnamed variable argument to specify the region index".to_string(),
            ));
            if d.args.len() != 1 {
                return err;
            }
            if let Elem::UnnamedVar(UnnamedVar { index, .. }) = &d.args[0] {
                let reg_parsed = format_ident!("reg_{}", index);
                state.regions.insert(*index, reg_parsed.clone());
                Ok(quote! {
                    let #reg_parsed = ::pliron::region::Region::parser
                        (state_stream.state.parent_for_regions).parse_stream(state_stream).into_result()?.0;
                })
            } else {
                return err;
            }
        } else if d.name == "attr" {
            let (attr_name_str, attr_type_path) = parse_attr_directive_args(d, input)?;
            let attr_name_ident = format_ident!("{}", attr_name_str);
            state
                .attributes
                .insert(attr_name_str.clone(), attr_name_ident.clone());
            Ok(quote! {
                let #attr_name_ident = Box::new(#attr_type_path::parser(())
                    .parse_stream(state_stream)
                    .into_result()?
                    .0);
            })
        } else {
            unimplemented!("Unknown directive {}", d.name)
        }
    }

    fn build_final_ret_value(_input: &FmtInput, state: &mut OpParserState) -> TokenStream {
        if !state.is_canonical {
            quote! {
                Ok(final_ret_value).into_parse_result()
            }
        } else {
            quote! {}
        }
    }

    /// Default implementation for building the parser's associated type for `Arg`.
    fn build_assoc_type_arg(_input: &FmtInput, _state: &mut OpParserState) -> Result<TokenStream> {
        Ok(quote! { Vec<(::pliron::identifier::Identifier, ::pliron::location::Location)> })
    }

    /// Default implementation for building the parser's associated type for `Parsed`.
    fn build_assoc_type_parsed(
        _input: &FmtInput,
        _state: &mut OpParserState,
    ) -> Result<TokenStream> {
        Ok(quote! { ::pliron::op::OpObj })
    }
}

struct DeriveAttributeParsable;

impl ParsableBuilder<()> for DeriveAttributeParsable {
    fn build_directive(_input: &FmtInput, _state: &mut (), d: &Directive) -> Result<TokenStream> {
        unimplemented!("Unknown directive {}", d.name)
    }
}

struct DeriveTypeParsable;

impl ParsableBuilder<()> for DeriveTypeParsable {
    fn build_directive(_input: &FmtInput, _state: &mut (), d: &Directive) -> Result<TokenStream> {
        unimplemented!("Unknown directive {}", d.name)
    }

    fn build_assoc_type_parsed(_input: &FmtInput, _state: &mut ()) -> Result<TokenStream> {
        Ok(quote! { ::pliron::r#type::TypePtr<Self> })
    }

    fn build_final_ret_value(_input: &FmtInput, _state: &mut ()) -> TokenStream {
        quote! {
            Ok(::pliron::r#type::Type::register_instance(final_ret_value, state_stream.state.ctx)).into_parse_result()
        }
    }
}

fn parse_attr_directive_args(d: &Directive, input: &FmtInput) -> Result<(String, syn::Type)> {
    if d.args.len() != 2 {
        return Err(syn::Error::new_spanned(
            input.ident.clone(),
            "The `attr` directive takes two arguments,
                        the first is attribute name, and second attribute type"
                .to_string(),
        ));
    }
    let Elem::Var(Var {
        name: attr_name, ..
    }) = &d.args[0]
    else {
        return Err(syn::Error::new_spanned(
            input.ident.clone(),
            "The first argument to `attr` directive must be a named variable representing its name"
                .to_string(),
        ));
    };
    let attr_type = match &d.args[1] {
                 Elem::Var(Var { name, .. }) => name.clone(),
                 Elem::Lit(lit) => {
                    lit.lit.clone()
                 }
                 _ =>
                return Err(syn::Error::new_spanned(
                    input.ident.clone(),
                    "The second argument to `attr` directive must be a named variable or a literal representing its type".to_string(),
                ))
            };
    let attr_type_path = syn::parse_str::<syn::Type>(&attr_type)?;
    let attr_name_str = attr_name.to_string();
    Ok((attr_name_str, attr_type_path))
}
