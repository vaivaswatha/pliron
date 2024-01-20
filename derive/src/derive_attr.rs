use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote, ToTokens};
use syn::{
    parse::{Parse, ParseStream},
    DeriveInput, Result,
};

use crate::{
    attr::{require_once, Attribute, AttributeName, DialectName, IRKind},
    derive_shared::{build_struct_body, VerifiersRegister},
};

struct DefAttributeInput {
    vis: syn::Visibility,
    ident: syn::Ident,
    generics: syn::Generics,
    attrs: Attrs,
    data: syn::Data,
}

impl Parse for DefAttributeInput {
    fn parse(input: ParseStream) -> Result<Self> {
        let input = DeriveInput::parse(input)?;
        Self::try_from(input)
    }
}

impl TryFrom<DeriveInput> for DefAttributeInput {
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
    attr_name: AttributeName,
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
        let mut attr_name = None;
        let mut attributes = vec![];

        for attr in input {
            if attr.path().is_ident("def_attribute") {
                continue;
            } else if attr.path().is_ident(DialectName::ATTR_NAME) {
                require_once(DialectName::ATTR_NAME, &dialect, attr)?;
                dialect = Some(DialectName::from_syn(attr)?);
            } else if attr.path().is_ident(AttributeName::ATTR_NAME) {
                require_once(AttributeName::ATTR_NAME, &attr_name, attr)?;
                match AttributeName::from_syn_opt_dialect(attr)? {
                    (Some(d), n) => {
                        require_once("dialect", &dialect, attr)?;
                        dialect = Some(d);
                        attr_name = Some(n);
                    }
                    (None, n) => {
                        attr_name = Some(n);
                    }
                }
            } else {
                attributes.push(attr.clone());
            }
        }

        Ok(Self {
            dialect: dialect
                .ok_or_else(|| err_struct_attrib_required(span, DialectName::ATTR_NAME))?,
            attr_name: attr_name
                .ok_or_else(|| err_struct_attrib_required(span, AttributeName::ATTR_NAME))?,
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

struct DefAttribute {
    input: DefAttributeInput,
    verifiers: VerifiersRegister,
}

impl From<DefAttributeInput> for DefAttribute {
    fn from(input: DefAttributeInput) -> Self {
        let verifiers = VerifiersRegister {
            ident: input.ident.clone(),
            verifiers_name: format_ident!("AttrInterfaceVerifier_{}", &input.ident),
            ifc_name: syn::parse_quote! { ::pliron::attribute::AttrInterfaceVerifier },
        };
        Self { input, verifiers }
    }
}

impl ToTokens for DefAttribute {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.extend(impl_attribute(self))
    }
}

fn impl_attribute(def_attrib: &DefAttribute) -> TokenStream {
    let verifiers_register = &def_attrib.verifiers;
    let input = &def_attrib.input;
    let name = &input.ident;

    let def_struct = {
        let attributes = &input.attrs.attributes;
        let kind = IRKind::Attribute;
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

    let impl_attribute_trait = {
        let dialect = &input.attrs.dialect;
        let attr_name = &input.attrs.attr_name;
        let verifiers_name = &verifiers_register.verifiers_name;

        quote! {
            impl ::pliron::attribute::Attribute for #name {
                fn eq_attr(&self, other: &dyn ::pliron::attribute::Attribute) -> bool {
                    other
                        .downcast_ref::<Self>()
                        .map_or(false, |other| other == self)
                }

                fn get_attr_id(&self) -> ::pliron::attribute::AttrId {
                    Self::get_attr_id_static()
                }

                fn get_attr_id_static() -> ::pliron::attribute::AttrId {
                    ::pliron::attribute::AttrId {
                        name: ::pliron::attribute::AttrName::new(#attr_name),
                        dialect: ::pliron::dialect::DialectName::new(#dialect),
                    }
                }

                fn verify_interfaces(&self, ctx: &::pliron::context::Context) -> ::pliron::error::Result<()> {
                    let interface_verifiers = ::inventory::iter::<#verifiers_name>();
                    for verifier in interface_verifiers {
                        (verifier.0)(self, ctx)?;
                    }
                    Ok(())
                }
            }
        }
    };

    quote! {
        #def_struct

        #verifiers_register

        #impl_attribute_trait
    }
}

pub(crate) fn def_attribute(input: impl Into<TokenStream>) -> syn::Result<TokenStream> {
    let input = syn::parse2::<DefAttributeInput>(input.into())?;
    let p = DefAttribute::from(input);
    Ok(p.into_token_stream())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple() {
        let input = quote! {
            #[def_attribute]
            #[attr_name = "testing.unit"]
            #[derive(PartialEq, Eq, Debug, Clone)]
            pub struct UnitAttr();
        };
        let got = def_attribute(input).unwrap();

        let want = quote! {
            #[derive(::pliron_derive::DeriveAttribDummy)]
            #[derive(PartialEq, Eq, Debug, Clone)]
            #[ir_kind = "attribute"]
            pub struct UnitAttr();

            #[allow (non_camel_case_types)]
            pub struct AttrInterfaceVerifier_UnitAttr(pub ::pliron::attribute::AttrInterfaceVerifier);
            impl UnitAttr {
                pub const fn build_interface_verifier(verifier: ::pliron::attribute::AttrInterfaceVerifier) -> AttrInterfaceVerifier_UnitAttr {
                    AttrInterfaceVerifier_UnitAttr(verifier)
                }
            }
            inventory::collect!(AttrInterfaceVerifier_UnitAttr);
            impl ::pliron::attribute::Attribute for UnitAttr {
                fn eq_attr(&self, other: &dyn ::pliron::attribute::Attribute) -> bool {
                    other.downcast_ref::<Self>().map_or(false, |other| other == self)
                }

                fn get_attr_id(&self) -> ::pliron::attribute::AttrId {
                    Self::get_attr_id_static()
                }

                fn get_attr_id_static() -> ::pliron::attribute::AttrId {
                    ::pliron::attribute::AttrId {
                        name: ::pliron::attribute::AttrName::new("unit"),
                        dialect: ::pliron::dialect::DialectName::new("testing"),
                    }
                }

                fn verify_interfaces(&self, ctx: &::pliron::context::Context) -> ::pliron::error::Result<()> {
                    let interface_verifiers = ::inventory::iter::<AttrInterfaceVerifier_UnitAttr>();
                    for verifier in interface_verifiers {
                        (verifier.0)(self, ctx)?;
                    }
                    Ok(())
                }
            }
            impl ::pliron::common_traits::Qualified for UnitAttr {
                type Qualifier = ::pliron::attribute::AttrId;

                fn get_qualifier(&self, ctx: &::pliron::context::Context) -> Self::Qualifier {
                    self.get_attr_id()
                }
            }
        };

        assert_eq!(want.to_string(), got.to_string());
    }
}
