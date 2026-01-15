use proc_macro2::{Span, TokenStream};
use quote::{ToTokens, quote};
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

        let fields = match input.data {
            syn::Data::Struct(ref data_struct) => data_struct.fields.clone(),
            _ => {
                return Err(syn::Error::new_spanned(
                    &input,
                    "Type can only be derived for structs",
                ));
            }
        };

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
            fields,
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
    fields: syn::Fields,
}

impl ImplType {
    fn generate_field_params(&self) -> TokenStream {
        match &self.fields {
            syn::Fields::Named(fields) => {
                let params = fields.named.iter().map(|field| {
                    let name = &field.ident;
                    let ty = &field.ty;
                    quote! { #name: #ty }
                });
                quote! { #(#params),* }
            }
            syn::Fields::Unnamed(fields) => {
                let params = fields.unnamed.iter().enumerate().map(|(i, field)| {
                    let name =
                        syn::Ident::new(&format!("field_{}", i), proc_macro2::Span::call_site());
                    let ty = &field.ty;
                    quote! { #name: #ty }
                });
                quote! { #(#params),* }
            }
            syn::Fields::Unit => quote! {},
        }
    }

    fn generate_field_assignments(&self) -> TokenStream {
        match &self.fields {
            syn::Fields::Named(fields) => {
                let assignments = fields.named.iter().map(|field| {
                    let name = &field.ident;
                    quote! { #name }
                });
                quote! { #(#assignments),* }
            }
            syn::Fields::Unnamed(fields) => {
                let assignments = fields.unnamed.iter().enumerate().map(|(i, _)| {
                    let name =
                        syn::Ident::new(&format!("field_{}", i), proc_macro2::Span::call_site());
                    quote! { #name }
                });
                quote! { #(#assignments),* }
            }
            syn::Fields::Unit => quote! {},
        }
    }
}

impl ToTokens for ImplType {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let name = &self.ident;
        let dialect = &self.dialect_name;
        let type_name = &self.type_name;
        let register = if self.fields.is_empty() {
            quote! {
                |ctx: &mut ::pliron::context::Context| {
                    #name::register_direct(ctx);
                    ::pliron::r#type::Type::register_instance(#name {}, ctx);
                }
            }
        } else {
            quote! {
                #name::register_direct
            }
        };

        let impl_get = if self.fields.is_empty() {
            let msg = LitStr::new(
                &format!("{} singleton not instantiated", type_name),
                Span::call_site(),
            );
            quote! {
                impl #name {
                    /// Get the singleton instance.
                    pub fn get(
                        ctx: &::pliron::context::Context
                    ) -> ::pliron::r#type::TypePtr<Self> {
                        ::pliron::r#type::Type::get_instance(
                            Self {},
                            ctx,
                        ).expect(#msg)
                    }
                }
            }
        } else {
            // Generate a factory method for structs with fields
            // We need to extract field information from the struct
            let field_params = self.generate_field_params();
            let field_assignments = self.generate_field_assignments();

            quote! {
                impl #name {
                    /// Get or create a new instance.
                    pub fn get(
                        ctx: &mut ::pliron::context::Context,
                        #field_params
                    ) -> ::pliron::r#type::TypePtr<Self> {
                        ::pliron::r#type::Type::register_instance(
                            #name {
                                #field_assignments
                            },
                            ctx,
                        )
                    }

                    pub fn get_existing(
                        ctx: & ::pliron::context::Context,
                        #field_params
                    ) -> ::std::option::Option<::pliron::r#type::TypePtr<Self>> {
                        ::pliron::r#type::Type::get_instance(
                            #name {
                                #field_assignments
                            },
                            ctx,
                        )
                    }
                }
            }
        };

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
                        for verifier in interface_verifiers {
                            verifier(self, ctx)?;
                        }
                    }
                    Ok(())
                }
            }

            #impl_get

            const _: () = {
                #[cfg_attr(not(target_family = "wasm"), ::pliron::linkme::distributed_slice(::pliron::context::CONTEXT_REGISTRATIONS), linkme(crate = ::pliron::linkme))]
                static TYPE_REGISTRATION: std::sync::LazyLock<::pliron::context::ContextRegistration> =
                    std::sync::LazyLock::new(||
                        #register
                    );

                #[cfg(target_family = "wasm")]
                ::pliron::inventory::submit! {
                    ::pliron::utils::inventory::LazyLockWrapper(&TYPE_REGISTRATION)
                }
            };
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
                        for verifier in interface_verifiers {
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
