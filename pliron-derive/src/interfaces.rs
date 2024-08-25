//! Attribute macros for defining and implementing Interfaces.

use quote::quote;
use quote::ToTokens;
use syn::parse::Parse;
use syn::parse_quote;
use syn::punctuated::Punctuated;
use syn::DeriveInput;
use syn::ItemImpl;
use syn::Path;
use syn::Token;
use syn::TypeParamBound;
use syn::{ItemTrait, Result};

/// This macro does two things:
/// 1. Prepends `::pliron::op::Op` as a super trait.
/// 2. Adds an entry in the `INTERFACE_DEPS` `distributed_slice` for each
///    super interface, so that verifiers of those can be run prior to this.
pub(crate) fn op_interface_define(
    input: proc_macro::TokenStream,
) -> Result<proc_macro2::TokenStream> {
    let mut r#trait = syn::parse2::<ItemTrait>(input.into())?;
    let intr_name = r#trait.ident.clone();
    // op::Op is always a supertrait for all Op Interfaces.
    let op_supertrait = syn::parse_str::<Path>("::pliron::op::Op")?;

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

    r#trait.supertraits = parse_quote! { #op_supertrait + #supertraits };

    // In an anonymous namespace, note down the super-interface dependencies in
    // our map, so that we can sort them all later for the verifiers to run.
    let deps_entry = quote! {
        const _: () = {
            #[linkme::distributed_slice(::pliron::op::OP_INTERFACE_DEPS)]
            static INTERFACE_DEP: std::sync::LazyLock<(std::any::TypeId, Vec<std::any::TypeId>)>
                = std::sync::LazyLock::new(|| {
                    (std::any::TypeId::of::<dyn #intr_name>(), vec![#(std::any::TypeId::of::<dyn #dep_interfaces>(),)*])
             });
        };
    };

    let mut output = r#trait.into_token_stream();
    output.extend(deps_entry);

    Ok(output)
}

/// This macro does two things:
/// 1. Mark that the Op be castable to the interface via type_to_trait.
/// 2. Register the trait verifier in the Op's list of interface verifiers.
pub(crate) fn op_interface_impl(
    input: proc_macro::TokenStream,
) -> Result<proc_macro2::TokenStream> {
    let r#impl = syn::parse2::<ItemImpl>(input.into())?;

    let Some((_, intr_name, _)) = r#impl.trait_.clone() else {
        return Err(syn::Error::new_spanned(
            r#impl,
            "#[op_interface_impl] must be specified on a Trait impl",
        ));
    };

    let op_name = (*r#impl.self_ty).clone();
    let trait_cast = quote! {
        ::pliron::type_to_trait!(#op_name, #intr_name);
    };

    let verifiers_entry = quote! {
        const _: () = {
            #[linkme::distributed_slice(pliron::op::OP_INTERFACE_VERIFIERS)]
            static INTERFACE_VERIFIER: std::sync::LazyLock<
                (pliron::op::OpId, (std::any::TypeId, ::pliron::op::OpInterfaceVerifier))
            > =
            std::sync::LazyLock::new(||
                (#op_name::get_opid_static(), (std::any::TypeId::of::<dyn #intr_name>(),
                     <#op_name as #intr_name>::verify))
            );
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
            #[::pliron_derive::op_interface_impl]
            impl #path for #struct_name {}
        }
    });

    let mut output = input.to_token_stream();
    output.extend(impls);

    Ok(output)
}
