use proc_macro2::TokenStream;
use quote::quote;
use syn::{
    Ident, LitStr, Token,
    parse::{Parse, ParseStream},
    punctuated::Punctuated,
};

/// Configuration for pliron entity definitions
#[derive(Default)]
struct EntityConfig {
    name: Option<LitStr>,
    format: Option<LitStr>,
    interfaces: Option<Vec<Ident>>,
    verifier: Option<LitStr>,
    generate_get: bool,
}

impl Parse for EntityConfig {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut config = EntityConfig::default();

        while !input.is_empty() {
            let key: Ident = input.parse()?;
            input.parse::<Token![=]>()?;

            match key.to_string().as_str() {
                "name" => {
                    config.name = Some(input.parse()?);
                }
                "format" => {
                    config.format = Some(input.parse()?);
                }
                "interfaces" => {
                    let content;
                    syn::bracketed!(content in input);
                    let interfaces: Punctuated<Ident, Token![,]> =
                        content.parse_terminated(Ident::parse, Token![,])?;
                    config.interfaces = Some(interfaces.into_iter().collect());
                }
                "verifier" => {
                    config.verifier = Some(input.parse()?);
                }
                "generate_get" => {
                    let value: syn::LitBool = input.parse()?;
                    config.generate_get = value.value;
                }
                _ => {
                    return Err(syn::Error::new(
                        key.span(),
                        format!("Unknown configuration key: {}", key),
                    ));
                }
            }

            if input.peek(Token![,]) {
                input.parse::<Token![,]>()?;
            }
        }

        Ok(config)
    }
}

/// Generate the expanded tokens for a pliron type definition
pub fn pliron_type(args: impl Into<TokenStream>, input: impl Into<TokenStream>) -> syn::Result<TokenStream> {
    let args = args.into();
    let input = input.into();
    let config = syn::parse2::<EntityConfig>(args)?;
    let input_tokens = TokenStream::from(input.clone());

    let mut expanded = quote! { #input_tokens };

    // Add def_type attribute
    if let Some(name) = &config.name {
        expanded = quote! {
            #[def_type(#name)]
            #expanded
        };
    }

    // Add format_type attribute
    if let Some(format) = &config.format {
        expanded = quote! {
            #[format_type(#format)]
            #expanded
        };
    } else {
        expanded = quote! {
            #[format_type]
            #expanded
        };
    }

    // Add derive_type_get if requested
    if config.generate_get {
        expanded = quote! {
            #[derive_type_get]
            #expanded
        };
    }

    // Add interface implementations if specified
    if let Some(interfaces) = &config.interfaces
        && !interfaces.is_empty()
    {
        let interface_list = quote! { #(#interfaces),* };
        expanded = quote! {
            #[derive_op_interface_impl(#interface_list)]
            #expanded
        };
    }

    // Add verifier implementation
    if let Some(verifier) = &config.verifier
        && verifier.value() == "succ"
    {
        let item: syn::Item = syn::parse2(input)?;
        if let syn::Item::Struct(struct_item) = item {
            let struct_name = &struct_item.ident;
            expanded = quote! {
                #expanded
                ::pliron::impl_verify_succ!(#struct_name);
            };
        }
    }

    Ok(expanded)
}

/// Generate the expanded tokens for a pliron attribute definition
pub fn pliron_attr(args: impl Into<TokenStream>, input: impl Into<TokenStream>) -> syn::Result<TokenStream> {
    let args = args.into();
    let input = input.into();
    let config = syn::parse2::<EntityConfig>(args)?;
    let input_tokens = TokenStream::from(input.clone());

    let mut expanded = quote! { #input_tokens };

    // Add def_attribute attribute
    if let Some(name) = &config.name {
        expanded = quote! {
            #[def_attribute(#name)]
            #expanded
        };
    }

    // Add format_attribute attribute
    if let Some(format) = &config.format {
        expanded = quote! {
            #[format_attribute(#format)]
            #expanded
        };
    } else {
        expanded = quote! {
            #[format_attribute]
            #expanded
        };
    }

    // Add interface implementations if specified
    if let Some(interfaces) = &config.interfaces
        && !interfaces.is_empty()
    {
        let interface_list = quote! { #(#interfaces),* };
        expanded = quote! {
            #[derive_op_interface_impl(#interface_list)]
            #expanded
        };
    }

    // Add verifier implementation
    if let Some(verifier) = &config.verifier
        && verifier.value() == "succ"
    {
        let item: syn::Item = syn::parse2(input)?;
        if let syn::Item::Struct(struct_item) = item {
            let struct_name = &struct_item.ident;
            expanded = quote! {
                #expanded
                ::pliron::impl_verify_succ!(#struct_name);
            };
        }
    }

    Ok(expanded)
}

/// Generate the expanded tokens for a pliron operation definition
pub fn pliron_op(args: impl Into<TokenStream>, input: impl Into<TokenStream>) -> syn::Result<TokenStream> {
    let args = args.into();
    let input = input.into();
    let config = syn::parse2::<EntityConfig>(args)?;
    let input_tokens = TokenStream::from(input.clone());

    let mut expanded = quote! { #input_tokens };

    // Add def_op attribute
    if let Some(name) = &config.name {
        expanded = quote! {
            #[def_op(#name)]
            #expanded
        };
    }

    // Add format_op attribute
    if let Some(format) = &config.format {
        expanded = quote! {
            #[format_op(#format)]
            #expanded
        };
    } else {
        expanded = quote! {
            #[format_op]
            #expanded
        };
    }

    // Add interface implementations if specified
    if let Some(interfaces) = &config.interfaces
        && !interfaces.is_empty()
    {
        let interface_list = quote! { #(#interfaces),* };
        expanded = quote! {
            #[derive_op_interface_impl(#interface_list)]
            #expanded
        };
    }

    // Add verifier implementation
    if let Some(verifier) = &config.verifier
        && verifier.value() == "succ"
    {
        let item: syn::Item = syn::parse2(input)?;
        if let syn::Item::Struct(struct_item) = item {
            let struct_name = &struct_item.ident;
            expanded = quote! {
                #expanded
                ::pliron::impl_verify_succ!(#struct_name);
            };
        }
    }

    Ok(expanded)
}

#[cfg(test)]
mod tests {
    use super::*;
    use expect_test::expect;
    use quote::quote;

    #[test]
    fn pliron_type_basic() {
        let args = quote! { name = "test.unit_type", verifier = "succ" };
        let input = quote! {
            #[derive(Debug, Clone, PartialEq, Eq, Hash)]
            pub struct UnitType;
        };
        let result = pliron_type(args, input).unwrap();
        let f = syn::parse2::<syn::File>(result).unwrap();
        let got = prettyplease::unparse(&f);

        expect![[r##"
            #[format_type]
            #[def_type("test.unit_type")]
            #[derive(Debug, Clone, PartialEq, Eq, Hash)]
            pub struct UnitType;
            ::pliron::impl_verify_succ!(UnitType);
        "##]]
        .assert_eq(&got);
    }

    #[test]
    fn pliron_type_with_format() {
        let args = quote! {
            name = "test.flags_type",
            format = "`type` `{` $flags `}`",
            verifier = "succ"
        };
        let input = quote! {
            #[derive(Debug, Clone, PartialEq, Eq, Hash)]
            struct FlagsType {
                flags: u32,
            }
        };
        let result = pliron_type(args, input).unwrap();
        let f = syn::parse2::<syn::File>(result).unwrap();
        let got = prettyplease::unparse(&f);

        expect![[r##"
            #[format_type("`type` `{` $flags `}`")]
            #[def_type("test.flags_type")]
            #[derive(Debug, Clone, PartialEq, Eq, Hash)]
            struct FlagsType {
                flags: u32,
            }
            ::pliron::impl_verify_succ!(FlagsType);
        "##]]
        .assert_eq(&got);
    }

    #[test]
    fn pliron_type_with_get() {
        let args = quote! {
            name = "test.vector_type",
            generate_get = true,
            verifier = "succ"
        };
        let input = quote! {
            #[derive(Debug, Clone, PartialEq, Eq, Hash)]
            struct VectorType {
                elem_ty: u32,
                num_elems: u32,
            }
        };
        let result = pliron_type(args, input).unwrap();
        let f = syn::parse2::<syn::File>(result).unwrap();
        let got = prettyplease::unparse(&f);

        expect![[r##"
            #[derive_type_get]
            #[format_type]
            #[def_type("test.vector_type")]
            #[derive(Debug, Clone, PartialEq, Eq, Hash)]
            struct VectorType {
                elem_ty: u32,
                num_elems: u32,
            }
            ::pliron::impl_verify_succ!(VectorType);
        "##]]
        .assert_eq(&got);
    }

    #[test]
    fn pliron_type_with_interfaces() {
        let args = quote! {
            name = "test.interface_type",
            interfaces = [Interface1, Interface2],
            verifier = "succ"
        };
        let input = quote! {
            #[derive(Debug, Clone, PartialEq, Eq, Hash)]
            struct InterfaceType;
        };
        let result = pliron_type(args, input).unwrap();
        let f = syn::parse2::<syn::File>(result).unwrap();
        let got = prettyplease::unparse(&f);

        expect![[r##"
            #[derive_op_interface_impl(Interface1, Interface2)]
            #[format_type]
            #[def_type("test.interface_type")]
            #[derive(Debug, Clone, PartialEq, Eq, Hash)]
            struct InterfaceType;
            ::pliron::impl_verify_succ!(InterfaceType);
        "##]]
        .assert_eq(&got);
    }

    #[test]
    fn pliron_attr_basic() {
        let args = quote! { name = "test.string_attr", verifier = "succ" };
        let input = quote! {
            #[derive(Debug, Clone, PartialEq, Eq, Hash)]
            struct StringAttr {
                value: String,
            }
        };
        let result = pliron_attr(args, input).unwrap();
        let f = syn::parse2::<syn::File>(result).unwrap();
        let got = prettyplease::unparse(&f);

        expect![[r##"
            #[format_attribute]
            #[def_attribute("test.string_attr")]
            #[derive(Debug, Clone, PartialEq, Eq, Hash)]
            struct StringAttr {
                value: String,
            }
            ::pliron::impl_verify_succ!(StringAttr);
        "##]]
        .assert_eq(&got);
    }

    #[test]
    fn pliron_attr_with_format() {
        let args = quote! {
            name = "test.string_attr",
            format = "`attr` `(` $value `)`",
            verifier = "succ"
        };
        let input = quote! {
            #[derive(Debug, Clone, PartialEq, Eq, Hash)]
            struct StringAttr {
                value: String,
            }
        };
        let result = pliron_attr(args, input).unwrap();
        let f = syn::parse2::<syn::File>(result).unwrap();
        let got = prettyplease::unparse(&f);

        expect![[r##"
            #[format_attribute("`attr` `(` $value `)`")]
            #[def_attribute("test.string_attr")]
            #[derive(Debug, Clone, PartialEq, Eq, Hash)]
            struct StringAttr {
                value: String,
            }
            ::pliron::impl_verify_succ!(StringAttr);
        "##]]
        .assert_eq(&got);
    }

    #[test]
    fn pliron_op_basic() {
        let args = quote! { name = "test.my_op", verifier = "succ" };
        let input = quote! {
            struct MyOp;
        };
        let result = pliron_op(args, input).unwrap();
        let f = syn::parse2::<syn::File>(result).unwrap();
        let got = prettyplease::unparse(&f);

        expect![[r##"
            #[format_op]
            #[def_op("test.my_op")]
            struct MyOp;
            ::pliron::impl_verify_succ!(MyOp);
        "##]]
        .assert_eq(&got);
    }

    #[test]
    fn pliron_op_with_format_and_interfaces() {
        let args = quote! {
            name = "test.if_op",
            format = "`(`$0`)` region($0)",
            interfaces = [OneOpdInterface, ZeroResultInterface, OneRegionInterface],
            verifier = "succ"
        };
        let input = quote! {
            struct IfOp;
        };
        let result = pliron_op(args, input).unwrap();
        let f = syn::parse2::<syn::File>(result).unwrap();
        let got = prettyplease::unparse(&f);

        expect![[r##"
            #[derive_op_interface_impl(OneOpdInterface, ZeroResultInterface, OneRegionInterface)]
            #[format_op("`(`$0`)` region($0)")]
            #[def_op("test.if_op")]
            struct IfOp;
            ::pliron::impl_verify_succ!(IfOp);
        "##]]
        .assert_eq(&got);
    }

    #[test]
    fn pliron_type_no_verifier() {
        let args = quote! { name = "test.simple_type" };
        let input = quote! {
            #[derive(Debug, Clone, PartialEq, Eq, Hash)]
            struct SimpleType;
        };
        let result = pliron_type(args, input).unwrap();
        let f = syn::parse2::<syn::File>(result).unwrap();
        let got = prettyplease::unparse(&f);

        expect![[r##"
            #[format_type]
            #[def_type("test.simple_type")]
            #[derive(Debug, Clone, PartialEq, Eq, Hash)]
            struct SimpleType;
        "##]]
        .assert_eq(&got);
    }

    #[test]
    fn pliron_attr_with_interfaces() {
        let args = quote! {
            name = "test.interface_attr",
            interfaces = [AttrInterface1, AttrInterface2]
        };
        let input = quote! {
            #[derive(Debug, Clone, PartialEq, Eq, Hash)]
            struct InterfaceAttr;
        };
        let result = pliron_attr(args, input).unwrap();
        let f = syn::parse2::<syn::File>(result).unwrap();
        let got = prettyplease::unparse(&f);

        expect![[r##"
            #[derive_op_interface_impl(AttrInterface1, AttrInterface2)]
            #[format_attribute]
            #[def_attribute("test.interface_attr")]
            #[derive(Debug, Clone, PartialEq, Eq, Hash)]
            struct InterfaceAttr;
        "##]]
        .assert_eq(&got);
    }

    #[test]
    fn entity_config_parse_error() {
        let args = quote! { unknown_key = "value" };
        let input = quote! { struct TestType; };
        let result = pliron_type(args, input);
        assert!(result.is_err());
        assert!(
            result
                .unwrap_err()
                .to_string()
                .contains("Unknown configuration key")
        );
    }

    #[test]
    fn pliron_type_all_options() {
        let args = quote! {
            name = "test.full_type",
            format = "`full` `<` $field `>`",
            interfaces = [Iface1, Iface2],
            verifier = "succ",
            generate_get = true
        };
        let input = quote! {
            #[derive(Debug, Clone, PartialEq, Eq, Hash)]
            struct FullType {
                field: u32,
            }
        };
        let result = pliron_type(args, input).unwrap();
        let f = syn::parse2::<syn::File>(result).unwrap();
        let got = prettyplease::unparse(&f);

        expect![[r##"
            #[derive_op_interface_impl(Iface1, Iface2)]
            #[derive_type_get]
            #[format_type("`full` `<` $field `>`")]
            #[def_type("test.full_type")]
            #[derive(Debug, Clone, PartialEq, Eq, Hash)]
            struct FullType {
                field: u32,
            }
            ::pliron::impl_verify_succ!(FullType);
        "##]]
        .assert_eq(&got);
    }
}
