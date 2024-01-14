use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote};
use syn::{
    parse::{Parse, ParseStream},
    Data, DeriveInput, Result,
};

use crate::{
    attr::{require_once, Attribute, DialectName, IRKind, OpName},
    derive_shared::impl_verifiers_register,
};

enum DefOpInput {
    Struct(Struct),
}

impl Parse for DefOpInput {
    fn parse(input: ParseStream) -> Result<Self> {
        let input = DeriveInput::parse(input)?;
        Self::try_from(input)
    }
}

impl TryFrom<DeriveInput> for DefOpInput {
    type Error = syn::Error;

    fn try_from(input: DeriveInput) -> Result<Self> {
        match input.data {
            Data::Struct(_) => Struct::try_from(input).map(DefOpInput::Struct),
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
    attrs: Attrs,
    ident: syn::Ident,
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
        Ok(Struct {
            attrs: Attrs::from_syn(input.ident.span(), &input.attrs)?,
            ident: input.ident,
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

    let def_struct = {
        let attributes = input.attrs.other;
        let kind = input.attrs.kind;

        quote! {
            #[derive(Clone, Copy)]
            #[derive(::pliron_derive::DeriveAttribDummy)]
            #(#attributes)*
            #kind
            pub struct #name { op: ::pliron::context::Ptr<::pliron::operation::Operation> }
        }
    };

    let verifiers_name = format_ident!("OpInterfaceVerifier_{}", name);
    let verifiers_register = impl_verifiers_register(
        name,
        &verifiers_name,
        quote! { ::pliron::op::OpInterfaceVerifier },
    );

    let dialect = input.attrs.dialect;
    let op_name = input.attrs.op_name;
    let impl_op_trait = quote! {
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
    };

    quote! {
        #def_struct

        #verifiers_register

        #impl_op_trait
    }
}

pub(crate) fn def_op(input: impl Into<TokenStream>) -> Result<TokenStream> {
    match syn::parse2::<DefOpInput>(input.into())? {
        DefOpInput::Struct(input) => Ok(impl_struct(input)),
    }
}
