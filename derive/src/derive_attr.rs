use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use syn::{Data, DataStruct, DeriveInput, Result};

use crate::{
    attr::{require_once, Attribute, AttributeName, DialectName, IRKind},
    derive_shared::{build_struct_body, derive_qualified, impl_verifiers_register},
};

enum Input<'a> {
    Struct(Struct<'a>),
}

impl<'a> Input<'a> {
    fn from_syn(input: &'a DeriveInput) -> Result<Self> {
        match &input.data {
            Data::Struct(data) => Struct::from_syn(input, data).map(Input::Struct),
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

struct Struct<'a> {
    attrs: Attrs,
    ident: &'a syn::Ident,
}

impl<'a> Struct<'a> {
    fn from_syn(input: &'a DeriveInput, _data: &'a DataStruct) -> Result<Self> {
        Ok(Self {
            ident: &input.ident,
            attrs: Attrs::from_syn(input.ident.span(), &input.attrs)?,
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

fn impl_struct(def: &DeriveInput, input: Struct) -> TokenStream {
    let name = &input.ident;

    let def_struct = {
        let attributes = input.attrs.attributes;
        let kind = IRKind::Attribute;
        let vis = &def.vis;
        let generics = &def.generics;
        let struct_body = build_struct_body(def);

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

pub(crate) fn def_attribute(input: DeriveInput) -> syn::Result<TokenStream> {
    let create_input = Input::from_syn(&input)?;
    match create_input {
        Input::Struct(strct) => Ok(impl_struct(&input, strct)),
    }
}
