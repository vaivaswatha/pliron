use proc_macro2::{Span, TokenStream};
use quote::{quote, ToTokens};
use syn::{
    parse::{Parse, ParseStream},
    DeriveInput, Result,
};

use crate::{
    attr::{require_once, Attribute, DialectName, IRKind, TypeName},
    derive_shared::{build_struct_body, ImplQualified},
};

struct DefTypeInput {
    vis: syn::Visibility,
    ident: syn::Ident,
    generics: syn::Generics,
    data: syn::Data,
    attrs: Attrs,
}

impl Parse for DefTypeInput {
    fn parse(input: ParseStream) -> Result<Self> {
        let input = DeriveInput::parse(input)?;
        Self::try_from(input)
    }
}

impl TryFrom<DeriveInput> for DefTypeInput {
    type Error = syn::Error;

    fn try_from(input: DeriveInput) -> Result<Self> {
        let attrs = Attrs::try_from(&input)?;
        let data @ syn::Data::Struct(_) = input.data else {
            return Err(syn::Error::new_spanned(
                &input,
                "Type can only be derived for structs",
            ));
        };
        Ok(Self {
            vis: input.vis,
            generics: input.generics,
            data,
            ident: input.ident,
            attrs,
        })
    }
}

struct Attrs {
    dialect: DialectName,
    type_name: TypeName,
    attributes: Vec<syn::Attribute>,
}

impl TryFrom<&DeriveInput> for Attrs {
    type Error = syn::Error;

    fn try_from(input: &DeriveInput) -> Result<Self> {
        Self::from_syn(input.ident.span(), &input.attrs)
    }
}

impl Attrs {
    fn from_syn(span: Span, input: &[syn::Attribute]) -> Result<Self> {
        let mut dialect = None;
        let mut type_name = None;
        let mut attributes = vec![];

        for attr in input {
            if attr.path().is_ident("def_type") {
                continue;
            } else if attr.path().is_ident(DialectName::ATTR_NAME) {
                require_once(DialectName::ATTR_NAME, &dialect, attr)?;
                dialect = Some(DialectName::from_syn(attr)?);
            } else if attr.path().is_ident(TypeName::ATTR_NAME) {
                require_once(TypeName::ATTR_NAME, &type_name, attr)?;
                match TypeName::from_syn_opt_dialect(attr)? {
                    (Some(d), n) => {
                        require_once("dialect", &dialect, attr)?;
                        dialect = Some(d);
                        type_name = Some(n);
                    }
                    (None, n) => {
                        type_name = Some(n);
                    }
                }
            } else {
                attributes.push(attr.clone());
            }
        }

        let Some(dialect) = dialect else {
            return Err(err_struct_attrib_required(span, "dialect"));
        };
        let Some(type_name) = type_name else {
            return Err(err_struct_attrib_required(span, "type_name"));
        };

        Ok(Self {
            dialect,
            type_name,
            attributes,
        })
    }
}

fn err_struct_attrib_required(span: Span, attr: &str) -> syn::Error {
    syn::Error::new(
        span,
        format!("{} attribute must be applied to the struct", attr),
    )
}

struct DefType {
    input: DefTypeInput,
    qualified: ImplQualified,
}

impl From<DefTypeInput> for DefType {
    fn from(input: DefTypeInput) -> Self {
        let qualified = ImplQualified {
            ident: input.ident.clone(),
            qualifier: syn::parse_quote! { ::pliron::r#type::TypeId },
            getter: quote! { self.get_type_id() },
        };
        Self { input, qualified }
    }
}

impl ToTokens for DefType {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.extend(impl_type(&self));
    }
}

fn impl_type(def_type: &DefType) -> TokenStream {
    let input = &def_type.input;
    let name = &input.ident;

    let def_struct = {
        let attributes = &input.attrs.attributes;
        let kind = IRKind::Type;
        let vis = &input.vis;
        let generics = &input.generics;
        let struct_body = match input.data {
            syn::Data::Struct(ref s) => build_struct_body(s),
            _ => unreachable!(),
        };

        quote! {
            #[derive(::pliron_derive::DeriveAttribDummy)]
            #(#attributes)*
            #kind
            #vis struct #name #generics #struct_body
        }
    };

    let impl_type = {
        let dialect = &input.attrs.dialect;
        let type_name = &input.attrs.type_name;

        quote! {
            impl ::pliron::r#type::Type for #name {
                fn hash_type(&self) -> ::pliron::storage_uniquer::TypeValueHash {
                    ::pliron::storage_uniquer::TypeValueHash::new(self)
                }

                fn eq_type(&self, other: &dyn ::pliron::r#type::Type) -> bool {
                    other
                        .downcast_ref::<Self>()
                        .map_or(false, |other| other == self)
                }

                fn get_type_id(&self) -> ::pliron::r#type::TypeId {
                    Self::get_type_id_static()
                }

                fn get_type_id_static() -> ::pliron::r#type::TypeId {
                    ::pliron::r#type::TypeId {
                        name: ::pliron::r#type::TypeName::new(#type_name),
                        dialect: ::pliron::dialect::DialectName::new(#dialect),
                    }
                }
            }
        }
    };

    let impl_qualified = &def_type.qualified;
    quote! {
        #def_struct

        #impl_type

        #impl_qualified
    }
}

pub(crate) fn def_type(input: impl Into<TokenStream>) -> syn::Result<TokenStream> {
    let input = syn::parse2::<DefTypeInput>(input.into())?;
    let p = DefType::from(input);
    Ok(p.into_token_stream())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple() {
        let input = quote! {
            #[def_type]
            #[type_name = "testing.simple_type"]
            #[derive(Hash, PartialEq, Eq, Debug)]
            pub struct SimpleType {}
        };

        let got = def_type(input).unwrap();

        let want = quote! {
            #[derive(::pliron_derive::DeriveAttribDummy)]
            #[derive(Hash, PartialEq, Eq, Debug)]
            #[ir_kind = "type"]
            pub struct SimpleType {}

            impl ::pliron::r#type::Type for SimpleType {
                fn hash_type(&self) -> ::pliron::storage_uniquer::TypeValueHash {
                    ::pliron::storage_uniquer::TypeValueHash::new(self)
                }

                fn eq_type(&self, other: &dyn ::pliron::r#type::Type) -> bool {
                    other.downcast_ref::<Self>().map_or(false, |other| other == self)
                }

                fn get_type_id(&self) -> ::pliron::r#type::TypeId {
                    Self::get_type_id_static()
                }

                fn get_type_id_static() -> ::pliron::r#type::TypeId {
                    ::pliron::r#type::TypeId {
                        name: ::pliron::r#type::TypeName::new("simple_type"),
                        dialect: ::pliron::dialect::DialectName::new("testing"),
                    }
                }
            }

            impl ::pliron::common_traits::Qualified for SimpleType {
                type Qualifier = ::pliron::r#type::TypeId;   // [get_qualifier]

                fn get_qualifier(&self, ctx: &::pliron::context::Context) -> Self::Qualifier {
                    self.get_type_id()
                }
            }
        };

        assert_eq!(want.to_string(), got.to_string());
    }
}
