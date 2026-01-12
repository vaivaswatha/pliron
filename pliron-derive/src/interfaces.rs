//! Attribute macros for defining and implementing Interfaces.

use quote::ToTokens;
use quote::quote;
use syn::DeriveInput;
use syn::Ident;
use syn::ItemImpl;
use syn::Path;
use syn::Token;
use syn::TypeParamBound;
use syn::parse::Parse;
use syn::parse_quote;
use syn::punctuated::Punctuated;
use syn::{ItemTrait, Result};

/// This macro does two things:
/// 1. Prepends `supertrait` as a super trait.
/// 2. Adds an entry in `interface_deps_slice` for each
///    super interface, so that verifiers of those can be run prior to this.
pub(crate) fn interface_define(
    input: proc_macro::TokenStream,
    supertrait: Path,
    verifier_type: Path,
    append_dyn_clone_trait: bool,
) -> Result<proc_macro2::TokenStream> {
    let mut r#trait = syn::parse2::<ItemTrait>(input.into())?;
    let intr_name = r#trait.ident.clone();
    let generics = r#trait.generics.clone();

    let dep_interfaces: Vec<_> = r#trait
        .supertraits
        .iter()
        .filter_map(|dep| {
            let TypeParamBound::Trait(trait_bound) = dep else {
                return None;
            };
            Some(trait_bound.path.clone())
        })
        .collect();
    let supertraits = r#trait.supertraits;

    // Create a method for getting super verifiers.
    let super_verifiers = quote! {
        fn super_verifiers() -> Vec<#verifier_type> where Self: Sized{
            vec![
                #(
                    <Self as #dep_interfaces>::verify
                ),*
            ]
        }
    };

    r#trait
        .items
        .push(syn::parse2::<syn::TraitItem>(super_verifiers)?);

    // Append main super trait (Op/Attribute/Type).
    r#trait.supertraits = parse_quote! { #supertrait + #supertraits };

    let mut output = r#trait.into_token_stream();
    if append_dyn_clone_trait {
        // https://github.com/kardeiz/objekt-clonable/blob/master/dyn-clonable-impl/src/lib.rs
        let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
        output.extend(quote! {
            ::pliron::dyn_clone::clone_trait_object!(#impl_generics #intr_name #ty_generics #where_clause);
        });
    }

    Ok(output)
}

/// This macro does two things:
/// 1. Mark that the rust type be castable to the interface via type_to_trait.
/// 2. Register the trait verifier in the rust type's list of interface verifiers.
pub(crate) fn interface_impl(
    input: proc_macro::TokenStream,
    interface_verifiers_slice: Path,
    id: Path,
    verifier_type: Path,
    super_verifiers_fn_type: Path,
    get_id_static: Ident,
) -> Result<proc_macro2::TokenStream> {
    let r#impl = syn::parse2::<ItemImpl>(input.into())?;

    let Some((_, intr_name, _)) = r#impl.trait_.clone() else {
        return Err(syn::Error::new_spanned(
            r#impl,
            "#[*_interface_impl] can be specified only on a trait impl",
        ));
    };

    let rust_ty = (*r#impl.self_ty).clone();
    let trait_cast = quote! {
        ::pliron::type_to_trait!(#rust_ty, #intr_name);
    };

    let verifiers_entry = quote! {
        const _: () = {
            #[cfg_attr(not(target_family = "wasm"), ::pliron::linkme::distributed_slice(#interface_verifiers_slice), linkme(crate = ::pliron::linkme))]
            static INTERFACE_VERIFIER: std::sync::LazyLock<
                (#id, (#verifier_type, #super_verifiers_fn_type))
            > =
            std::sync::LazyLock::new(||
                (#rust_ty::#get_id_static(),
                     (<#rust_ty as #intr_name>::verify, <#rust_ty as #intr_name>::super_verifiers))
            );

            #[cfg(target_family = "wasm")]
            ::pliron::inventory::submit! {
                ::pliron::utils::inventory::LazyLockWrapper(&INTERFACE_VERIFIER)
            }
        };
    };

    let mut output = r#impl.to_token_stream();
    output.extend(trait_cast);
    output.extend(verifiers_entry);

    Ok(output)
}

struct PathList {
    paths: Vec<Path>,
}

impl Parse for PathList {
    fn parse(input: syn::parse::ParseStream) -> Result<Self> {
        let paths = Punctuated::<Path, Token![,]>::parse_terminated(input)?;
        Ok(PathList {
            paths: paths.into_iter().collect(),
        })
    }
}

/// For each interface specified in the list, expand it to
/// ```no_compile
/// #[op_interface_impl]
/// impl Interface for OpStruct { }
/// ```
pub(crate) fn derive_op_interface_impl(
    attr: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> Result<proc_macro2::TokenStream> {
    let intrs = syn::parse2::<PathList>(attr.into())?;
    let input = syn::parse2::<DeriveInput>(input.into())?;
    let struct_name = input.ident.clone();

    let impls = intrs.paths.into_iter().map(|path| {
        quote! {
            #[::pliron::derive::op_interface_impl]
            impl #path for #struct_name {}
        }
    });

    let mut output = input.to_token_stream();
    output.extend(impls);

    Ok(output)
}
