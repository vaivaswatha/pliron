use proc_macro2::TokenStream;
use quote::quote;
use syn::{DataStruct, DeriveInput};

pub(crate) fn derive_qualified(
    type_name: &syn::Ident,
    qualifier: TokenStream,
    body: TokenStream,
) -> TokenStream {
    quote! {
        impl ::pliron::common_traits::Qualified for #type_name {
            type Qualifier = #qualifier;

            fn get_qualifier(&self, ctx: &::pliron::context::Context) -> Self::Qualifier {
                #body
            }
        }
    }
}

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

pub(crate) fn impl_verifiers_register(
    name: &syn::Ident,
    verifiers_name: &syn::Ident,
    ifc: TokenStream,
) -> proc_macro2::TokenStream {
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
}
