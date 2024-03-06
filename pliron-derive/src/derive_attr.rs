use proc_macro2::TokenStream;
use quote::{format_ident, quote, ToTokens};
use syn::{DeriveInput, LitStr, Result};

const PROC_MACRO_NAME: &str = "def_attribute";

use crate::{
    derive_shared::{mark_ir_kind, VerifiersRegister},
    macro_attr::IRKind,
};

pub(crate) fn def_attribute(
    args: impl Into<TokenStream>,
    input: impl Into<TokenStream>,
) -> syn::Result<TokenStream> {
    let name = syn::parse2::<LitStr>(args.into())?;
    let input = syn::parse2::<DeriveInput>(input.into())?;
    let p = DefAttribute::derive(name, input)?;
    Ok(p.into_token_stream())
}

/// The derived macro body for the `#[def_attribute]` proc macro.
struct DefAttribute {
    input: DeriveInput,
    impl_attr: ImplAttribute,
    verifiers: VerifiersRegister,
}

impl DefAttribute {
    fn derive(name: LitStr, input: DeriveInput) -> Result<Self> {
        let name_str = name.value();
        let Some((dialect_name, attr_name)) = name_str.split_once('.') else {
            return Err(syn::Error::new_spanned(
                name,
                "attribute name must be in the form of `dialect.attr_name`",
            ));
        };

        match input.data {
            syn::Data::Struct(_) => {}
            _ => {
                return Err(syn::Error::new_spanned(
                    &input,
                    "Attribute can only be derived for structs",
                ));
            }
        }

        if !input.generics.params.is_empty() {
            return Err(syn::Error::new_spanned(
                &input,
                "Attribute cannot be derived for generic structs",
            ));
        }

        let attrs = input
            .attrs
            .into_iter()
            .filter(|attr| !attr.path().is_ident(PROC_MACRO_NAME));
        let attrs: Vec<_> = mark_ir_kind(attrs, IRKind::Attribute).collect();

        let input = DeriveInput { attrs, ..input };

        let verifiers = VerifiersRegister {
            ident: input.ident.clone(),
            verifiers_name: format_ident!("AttrInterfaceVerifier_{}", &input.ident),
            ifc_name: syn::parse_quote! { ::pliron::attribute::AttrInterfaceVerifier },
        };

        let impl_attr = ImplAttribute {
            ident: input.ident.clone(),
            dialect_name: dialect_name.to_string(),
            attr_name: attr_name.to_string(),
            verifiers_name: verifiers.verifiers_name.clone(),
        };

        Ok(Self {
            input,
            impl_attr,
            verifiers,
        })
    }
}

impl ToTokens for DefAttribute {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let def_struct = &self.input;
        let verifiers_register = &self.verifiers;
        let impl_attribute_trait = &self.impl_attr;
        tokens.extend(quote! {
            #def_struct

            #verifiers_register

            #impl_attribute_trait
        });
    }
}

struct ImplAttribute {
    ident: syn::Ident,
    attr_name: String,
    dialect_name: String,
    verifiers_name: syn::Ident,
}

impl ToTokens for ImplAttribute {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let name = &self.ident;
        let attr_name = &self.attr_name;
        let dialect = &self.dialect_name;
        let verifiers_name = &self.verifiers_name;
        tokens.extend(quote! {
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

        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use expect_test::expect;

    #[test]
    fn simple() {
        let args = quote! { "testing.unit" };
        let input = quote! {
            #[def_attribute("testing.unit")]
            #[derive(PartialEq, Eq, Debug, Clone)]
            pub struct UnitAttr();
        };
        let attr = def_attribute(args, input).unwrap();
        let f = syn::parse2::<syn::File>(attr).unwrap();
        let got = prettyplease::unparse(&f);

        expect![[r##"
            #[derive(PartialEq, Eq, Debug, Clone)]
            #[derive(::pliron_derive::DeriveAttribAcceptor)]
            #[ir_kind = "attribute"]
            pub struct UnitAttr();
            #[allow(non_camel_case_types)]
            pub struct AttrInterfaceVerifier_UnitAttr(
                pub ::pliron::attribute::AttrInterfaceVerifier,
            );
            impl UnitAttr {
                pub const fn build_interface_verifier(
                    verifier: ::pliron::attribute::AttrInterfaceVerifier,
                ) -> AttrInterfaceVerifier_UnitAttr {
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
                fn verify_interfaces(
                    &self,
                    ctx: &::pliron::context::Context,
                ) -> ::pliron::error::Result<()> {
                    let interface_verifiers = ::inventory::iter::<AttrInterfaceVerifier_UnitAttr>();
                    for verifier in interface_verifiers {
                        (verifier.0)(self, ctx)?;
                    }
                    Ok(())
                }
            }
        "##]]
        .assert_eq(&got);
    }
}
