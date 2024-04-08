use proc_macro2::TokenStream;
use quote::{quote, ToTokens};

use crate::macro_attr::IRKind;

/// VerifiersRegister represents the [inventory] types and implementations
/// required to by Op and Attribute IR entities.
pub struct VerifiersRegister {
    pub ident: syn::Ident,
    pub verifiers_name: syn::Ident,
    pub ifc_name: syn::Path,
}

impl ToTokens for VerifiersRegister {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let name = &self.ident;
        let verifiers_name = &self.verifiers_name;
        let ifc = &self.ifc_name;
        quote! {
            #[allow(non_camel_case_types)]
            pub struct #verifiers_name(pub #ifc);

            impl #name {
                #[doc(hidden)]
                pub const fn build_interface_verifier(verifier: #ifc) -> #verifiers_name {
                    #verifiers_name(verifier)
                }
            }

            inventory::collect!(#verifiers_name);
        }
        .to_tokens(tokens);
    }
}

pub(crate) fn mark_ir_kind(
    attrs: impl Iterator<Item = syn::Attribute>,
    kind: IRKind,
) -> impl Iterator<Item = syn::Attribute> {
    attrs
        .chain(std::iter::once(syn::parse_quote! {
            #[derive(::pliron_derive::DeriveAttribAcceptor)]
        }))
        .chain(std::iter::once(syn::parse_quote! {
            #kind
        }))
}
