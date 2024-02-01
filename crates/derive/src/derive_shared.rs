use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use syn::DataStruct;

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
                pub const fn build_interface_verifier(verifier: #ifc) -> #verifiers_name {
                    #verifiers_name(verifier)
                }
            }

            inventory::collect!(#verifiers_name);
        }
        .to_tokens(tokens);
    }
}

/// Helper function to create a token stream for the fields of a struct.
pub(crate) fn build_struct_body(ds: &DataStruct) -> proc_macro2::TokenStream {
    match ds.fields {
        syn::Fields::Named(_) => {
            let it = ds.fields.iter();
            quote::quote! {
                { #(#it),* }
            }
        }
        syn::Fields::Unnamed(_) => {
            let it = ds.fields.iter();
            quote::quote! {
                ( #(#it),* );
            }
        }
        syn::Fields::Unit => quote::quote! { (); },
    }
}
