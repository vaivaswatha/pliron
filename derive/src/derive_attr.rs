use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use syn::{
    parse::{Parse, ParseStream},
    Data, DeriveInput, Result,
};

use crate::{
    attr::{require_once, Attribute, AttributeName, DialectName, IRKind},
    derive_shared::{build_struct_body, derive_qualified, impl_verifiers_register},
};

enum DefAttributeInput {
    Struct(Struct),
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
        match input.data {
            Data::Struct(_) => Struct::try_from(input).map(DefAttributeInput::Struct),
            Data::Enum(_) => Err(syn::Error::new_spanned(
                input,
                "Type can only be derived for structs",
            )),
            Data::Union(_) => Err(syn::Error::new_spanned(
                input,
                "Type can only be derived for structs",
            )),
        }
    }
}

struct Struct {
    vis: syn::Visibility,
    ident: syn::Ident,
    generics: syn::Generics,
    data: syn::DataStruct,
    attrs: Attrs,
}

impl TryFrom<DeriveInput> for Struct {
    type Error = syn::Error;

    fn try_from(input: DeriveInput) -> Result<Self> {
        let syn::Data::Struct(data) = input.data else {
            return Err(syn::Error::new_spanned(
                input,
                "Type can only be derived for structs",
            ));
        };
        let attrs = Attrs::from_syn(input.ident.span(), &input.attrs)?;
        Ok(Struct {
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

impl Attrs {
    fn from_syn(span: Span, input: &[syn::Attribute]) -> Result<Self> {
        let mut dialect = None;
        let mut attr_name = None;
        let mut attributes = vec![];

        for attr in input {
            if attr.path().is_ident(DialectName::ATTR_NAME) {
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

fn impl_struct(input: Struct) -> TokenStream {
    let name = &input.ident;

    let def_struct = {
        let attributes = input.attrs.attributes;
        let kind = IRKind::Attribute;
        let vis = &input.vis;
        let generics = &input.generics;
        let struct_body = build_struct_body(&input.data);

        quote! {
            #[derive(::pliron_derive::DeriveAttribDummy)]
            #(#attributes)*
            #kind
            #vis struct #name #generics #struct_body
        }
    };

    let verifiers_name = format_ident!("AttrInterfaceVerifier_{}", name);
    let verifiers_register = impl_verifiers_register(
        name,
        &verifiers_name,
        quote! { ::pliron::attribute::AttrInterfaceVerifier },
    );

    let impl_attribute_trait = {
        let dialect = input.attrs.dialect;
        let attr_name = input.attrs.attr_name;

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

                fn verify_interfaces(&self, ctx: &Context) -> ::pliron::error::Result<()> {
                    let interface_verifiers = ::inventory::iter::<#verifiers_name>;
                    for verifier in interface_verifiers {
                        (verifier.0)(self, ctx)?;
                    }
                    Ok(())
                }
            }
        }
    };

    let impl_qualified_trait = derive_qualified(
        name,
        quote! { ::pliron::attribute::AttrId },
        quote! { self.get_attr_id() },
    );

    quote! {
        #def_struct
        #verifiers_register

        #impl_attribute_trait
        #impl_qualified_trait
    }
}

pub(crate) fn def_attribute(input: impl Into<TokenStream>) -> syn::Result<TokenStream> {
    match syn::parse2::<DefAttributeInput>(input.into())? {
        DefAttributeInput::Struct(strct) => Ok(impl_struct(strct)),
    }
}
