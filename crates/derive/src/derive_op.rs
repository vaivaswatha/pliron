use proc_macro2::{Span, TokenStream};
use quote::{format_ident, quote, ToTokens};
use syn::{
    parse::{Parse, ParseStream},
    DeriveInput, Result,
};

use crate::{
    attr::{require_once, Attribute, DialectName, IRKind, OpName},
    derive_shared::VerifiersRegister,
};

struct DefOpInput {
    attrs: Attrs,
    ident: syn::Ident,
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
        let syn::Data::Struct(_) = input.data else {
            return Err(syn::Error::new_spanned(
                input,
                "Type can only be derived for structs",
            ));
        };
        Ok(Self {
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
            if attr.path().is_ident("def_op") {
                continue;
            } else if attr.path().is_ident(DialectName::ATTR_NAME) {
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

struct DefOp {
    input: DefOpInput,
    verifiers: VerifiersRegister,
}

impl From<DefOpInput> for DefOp {
    fn from(input: DefOpInput) -> Self {
        let verifiers = VerifiersRegister {
            ident: input.ident.clone(),
            verifiers_name: format_ident!("OpInterfaceVerifier_{}", &input.ident),
            ifc_name: syn::parse_quote! { ::pliron::op::OpInterfaceVerifier },
        };
        Self { input, verifiers }
    }
}

impl ToTokens for DefOp {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.extend(impl_op(&self));
    }
}

fn impl_op(input: &DefOp) -> TokenStream {
    let verifiers_register = &input.verifiers;
    let input = &input.input;
    let name = &input.ident;

    let def_struct = {
        let attributes = &input.attrs.other;
        let kind = input.attrs.kind;

        quote! {
            #[derive(Clone, Copy)]
            #[derive(::pliron_derive::DeriveAttribDummy)]
            #(#attributes)*
            #kind
            pub struct #name { op: ::pliron::context::Ptr<::pliron::operation::Operation> }
        }
    };

    let dialect = &input.attrs.dialect;
    let op_name = &input.attrs.op_name;
    let verifiers_name = &verifiers_register.verifiers_name;
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

            fn verify_interfaces(&self, ctx: &::pliron::context::Context) -> ::pliron::error::Result<()> {
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
    let input = syn::parse2::<DefOpInput>(input.into())?;
    let p = DefOp::from(input);
    Ok(p.into_token_stream())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple() {
        let input = quote! {
            #[def_op]
            #[op_name="testing.testop"]
            struct TestOp;
        };
        let got = def_op(input).unwrap();

        let want = quote! {
            #[derive(Clone, Copy)]
            #[derive(::pliron_derive::DeriveAttribDummy)]
            #[ir_kind = "op"]
            pub struct TestOp {
                op: ::pliron::context::Ptr<::pliron::operation::Operation>
            }

            #[allow(non_camel_case_types)]
            pub struct OpInterfaceVerifier_TestOp(pub ::pliron::op::OpInterfaceVerifier);
            impl TestOp {
                pub const fn build_interface_verifier(
                    verifier: ::pliron::op::OpInterfaceVerifier
                ) -> OpInterfaceVerifier_TestOp {
                    OpInterfaceVerifier_TestOp(verifier)
                }
            }

            inventory::collect!(OpInterfaceVerifier_TestOp);

            impl ::pliron::op::Op for TestOp {
                fn get_operation(&self) -> ::pliron::context::Ptr<::pliron::operation::Operation> {
                    self.op
                }
                fn wrap_operation(
                    op: ::pliron::context::Ptr<::pliron::operation::Operation>
                ) -> ::pliron::op::OpObj {
                    Box::new(TestOp { op })
                }
                fn get_opid(&self) -> ::pliron::op::OpId {
                    Self::get_opid_static()
                }
                fn get_opid_static() -> ::pliron::op::OpId {
                    ::pliron::op::OpId {
                        name: ::pliron::op::OpName::new("testop"),
                        dialect: ::pliron::dialect::DialectName::new("testing"),
                    }
                }
                fn verify_interfaces(&self, ctx: &::pliron::context::Context) -> ::pliron::error::Result<()> {
                    let interface_verifiers = ::inventory::iter::<OpInterfaceVerifier_TestOp>;
                    for verifier in interface_verifiers {
                        (verifier.0)(self, ctx)?;
                    }
                    Ok(())
                }
            }
        };

        assert_eq!(want.to_string(), got.to_string());
    }
}
