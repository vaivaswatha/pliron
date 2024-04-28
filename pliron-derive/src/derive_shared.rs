use crate::macro_attr::IRKind;

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
