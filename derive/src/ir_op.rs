use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use syn::{Data, DataStruct, DeriveInput, Result};

use crate::attr::{require_once, Attribute, DialectName, IRKind, OpName};

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
    op_name: OpName,
    kind: IRKind,
    other: Vec<syn::Attribute>,
}

impl Attrs {
    fn from_syn(span: Span, input: &[syn::Attribute]) -> Result<Self> {
        let mut dialect = None;
        let mut op_name = None;
        let mut kind = None;
        let mut other = vec![];

        for attr in input {
            if attr.path().is_ident(DialectName::ATTR_NAME) {
                require_once(DialectName::ATTR_NAME, &dialect, attr)?;
                dialect = Some(DialectName::from_syn(attr)?);
            } else if attr.path().is_ident(IRKind::ATTR_NAME) {
                require_once(IRKind::ATTR_NAME, &kind, attr)?;
                kind = Some(IRKind::from_syn(attr)?);
            } else if attr.path().is_ident(OpName::ATTR_NAME) {
                require_once(OpName::ATTR_NAME, &op_name, attr)?;
                match OpName::from_syn_opt_dialect(attr)? {
                    (Some(d), n) => {
                        require_once("dialect", &dialect, attr)?;
                        dialect = Some(d);
                        op_name = Some(n);
                    }
                    (None, n) => {
                        op_name = Some(n);
                    }
                }
            } else {
                other.push(attr.clone());
            }
        }

        Ok(Self {
            dialect: dialect
                .ok_or_else(|| err_struct_attrib_required(span, DialectName::ATTR_NAME))?,
            kind: kind.unwrap_or(IRKind::Op),
            op_name: op_name.ok_or_else(|| err_struct_attrib_required(span, OpName::ATTR_NAME))?,
            other,
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
    let verifiers_name = format_ident!("OpInterfaceVerifier_{}", name);
    let dialect = input.attrs.dialect;
    let op_name = input.attrs.op_name;
    let kind = input.attrs.kind;
    let attributes = input.attrs.other;
    quote! {
        #[derive(Clone, Copy)]
        #(#attributes)*
        #kind
        pub struct #name { op: ::pliron::context::Ptr<::pliron::operation::Operation> }

        #[allow(non_camel_case_types)]
        pub struct #verifiers_name(pub ::pliron::op::OpInterfaceVerifier);

        impl #name {
            pub const fn build_interface_verifier(verifier: ::pliron::op::OpInterfaceVerifier) -> #verifiers_name {
                #verifiers_name(verifier)
            }
        }

        inventory::collect!(#verifiers_name);

        impl ::pliron::op::Op for #name {
            fn get_operation(&self) -> ::pliron::context::Ptr<::pliron::operation::Operation> {
                self.op
            }

            fn wrap_operation(op: ::pliron::context::Ptr<::pliron::operation::Operation>) -> ::pliron::op::OpObj {
                Box::new(#name { op })
            }

            fn get_opid(&self) -> ::pliron::op::OpId {
                Self::get_opid_static()
            }

            fn get_opid_static() -> ::pliron::op::OpId {
                ::pliron::op::OpId {
                    name: ::pliron::op::OpName::new(#op_name),
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
}

pub(crate) fn declare(input: DeriveInput) -> syn::Result<proc_macro2::TokenStream> {
    let input = Input::from_syn(&input)?;
    match input {
        Input::Struct(input) => Ok(impl_struct(input)),
    }
}
