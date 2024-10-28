use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use syn::{DeriveInput, LitStr, Result};

const PROC_MACRO_NAME: &str = "def_type";

pub(crate) fn def_type(
    args: impl Into<TokenStream>,
    input: impl Into<TokenStream>,
) -> syn::Result<TokenStream> {
    let name = syn::parse2::<LitStr>(args.into())?;
    let input = syn::parse2::<DeriveInput>(input.into())?;
    let p = DefType::derive(name, input)?;
    Ok(p.into_token_stream())
}

/// Input for the `#[def_type]` proc macro.
struct DefType {
    input: DeriveInput,
    impl_type: ImplType,
}

impl DefType {
    fn derive(name: LitStr, input: DeriveInput) -> Result<Self> {
        let name_str = name.value();
        let Some((dialect_name, type_name)) = name_str.split_once('.') else {
            return Err(syn::Error::new_spanned(
                name,
                "type name must be in the form `dialect.type_name`",
            ));
        };

        match input.data {
            syn::Data::Struct(_) => {}
            _ => {
                return Err(syn::Error::new_spanned(
                    &input,
                    "Type can only be derived for structs",
                ));
            }
        }
        if !input.generics.params.is_empty() {
            return Err(syn::Error::new_spanned(
                &input,
                "Type cannot be derived for generic structs",
            ));
        }

        let attrs = input
            .attrs
            .into_iter()
            .filter(|attr| !attr.path().is_ident(PROC_MACRO_NAME))
            .collect();

        let input = DeriveInput { attrs, ..input };

        let impl_type = ImplType {
            ident: input.ident.clone(),
            dialect_name: dialect_name.to_string(),
            type_name: type_name.to_string(),
        };
        Ok(Self { input, impl_type })
    }
}

impl ToTokens for DefType {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let def_struct = &self.input;
        let impl_type = &self.impl_type;
        tokens.extend(quote! {
            #def_struct

            #impl_type
        });
    }
}

struct ImplType {
    ident: syn::Ident,
    dialect_name: String,
    type_name: String,
}

impl ToTokens for ImplType {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let name = &self.ident;
        let dialect = &self.dialect_name;
        let type_name = &self.type_name;
        tokens.extend(quote! {
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

                fn verify_interfaces(&self, ctx: &::pliron::context::Context) -> ::pliron::result::Result<()> {
                    if let Some(interface_verifiers) =
                        ::pliron::r#type::TYPE_INTERFACE_VERIFIERS_MAP.get(&Self::get_type_id_static())
                    {
                        for (_, verifier) in interface_verifiers {
                            verifier(self, ctx)?;
                        }
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
        let args = quote! { "testing.simple_type" };
        let input = quote! {
            #[derive(Hash, PartialEq, Eq, Debug)]
            pub struct SimpleType;
        };
        let t = def_type(args, input).unwrap();
        let f = syn::parse2::<syn::File>(t).unwrap();
        let got = prettyplease::unparse(&f);

        expect![[r##"
            #[derive(Hash, PartialEq, Eq, Debug)]
            pub struct SimpleType;
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
                fn verify_interfaces(
                    &self,
                    ctx: &::pliron::context::Context,
                ) -> ::pliron::result::Result<()> {
                    if let Some(interface_verifiers) = ::pliron::r#type::TYPE_INTERFACE_VERIFIERS_MAP
                        .get(&Self::get_type_id_static())
                    {
                        for (_, verifier) in interface_verifiers {
                            verifier(self, ctx)?;
                        }
                    }
                    Ok(())
                }
            }
        "##]]
        .assert_eq(&got);
    }
}
