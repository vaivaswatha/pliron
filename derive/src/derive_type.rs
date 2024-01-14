use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::{Data, DataStruct, DeriveInput, Result};

use crate::{
    attr::{require_once, Attribute, DialectName, IRKind, TypeName},
    derive_shared::{build_struct_body, derive_qualified},
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
    type_name: TypeName,
    attributes: Vec<syn::Attribute>,
}

impl Attrs {
    fn from_syn(span: Span, input: &[syn::Attribute]) -> Result<Self> {
        let mut dialect = None;
        let mut type_name = None;
        let mut attributes = vec![];

        for attr in input {
            if attr.path().is_ident(DialectName::ATTR_NAME) {
                require_once(DialectName::ATTR_NAME, &dialect, attr)?;
                dialect = Some(DialectName::from_syn(attr)?);
            } else if attr.path().is_ident(TypeName::ATTR_NAME) {
                require_once(TypeName::ATTR_NAME, &type_name, attr)?;
                match TypeName::from_syn_opt_dialect(attr)? {
                    (Some(d), n) => {
                        require_once("dialect", &dialect, attr)?;
                        dialect = Some(d);
                        type_name = Some(n);
                    }
                    (None, n) => {
                        type_name = Some(n);
                    }
                }
            } else {
                attributes.push(attr.clone());
            }
        }

        let Some(dialect) = dialect else {
            return Err(err_struct_attrib_required(span, "dialect"));
        };
        let Some(type_name) = type_name else {
            return Err(err_struct_attrib_required(span, "type_name"));
        };

        Ok(Self {
            dialect,
            type_name,
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
        let kind = IRKind::Type;
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

    let dialect = input.attrs.dialect;
    let type_name = input.attrs.type_name;
    let impl_type = quote! {
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
        }
    };

    let impl_qualified = derive_qualified(
        name,
        quote! { ::pliron::r#type::TypeId },
        quote! { self.get_type_id() },
    );

    quote! {
        #def_struct
        #impl_type
        #impl_qualified
    }
}

pub(crate) fn def_type(input: DeriveInput) -> syn::Result<TokenStream> {
    let create_input = Input::from_syn(&input)?;
    match create_input {
        Input::Struct(strct) => Ok(impl_struct(&input, strct)),
    }
}
