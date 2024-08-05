use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use syn::{DeriveInput, LitStr, Result};

use crate::{derive_shared::mark_ir_kind, macro_attr::IRKind};

const PROC_MACRO_NAME: &str = "def_op";

pub(crate) fn def_op(
    args: impl Into<TokenStream>,
    input: impl Into<TokenStream>,
) -> Result<TokenStream> {
    let name = syn::parse2::<LitStr>(args.into())?;
    let input = syn::parse2::<DeriveInput>(input.into())?;
    let p = DefOp::derive(name, input)?;
    Ok(p.into_token_stream())
}

/// The derived macro body for the `#[def_attribute]` proc macro.
struct DefOp {
    input: DeriveInput,
    impl_op: ImplOp,
}

impl DefOp {
    fn derive(name: LitStr, input: DeriveInput) -> Result<Self> {
        let name_str = name.value();
        let Some((dialect_name, op_name)) = name_str.split_once('.') else {
            return Err(syn::Error::new_spanned(
                name,
                "op_name must be in the form `dialect.op_name`",
            ));
        };

        let syn::Data::Struct(ref struct_data) = input.data else {
            return Err(syn::Error::new_spanned(
                &input,
                "Type can only be derived for structs",
            ));
        };
        if !struct_data.fields.is_empty() {
            return Err(syn::Error::new_spanned(
                &struct_data.fields,
                "Op struct cannot have custom fields",
            ));
        }
        if !input.generics.params.is_empty() {
            return Err(syn::Error::new_spanned(
                &input,
                "Op cannot be derived for generic structs",
            ));
        }

        let attrs = input
            .attrs
            .into_iter()
            .filter(|attr| !attr.path().is_ident(PROC_MACRO_NAME));
        let attrs: Vec<_> = mark_ir_kind(attrs, IRKind::Op).collect();

        let input = DeriveInput { attrs, ..input };

        let impl_op = ImplOp {
            struct_name: input.ident.clone(),
            dialect_name: dialect_name.to_string(),
            op_name: op_name.to_string(),
        };
        Ok(Self { input, impl_op })
    }
}

impl ToTokens for DefOp {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let def_struct = {
            let vis = &self.input.vis;
            let attributes = &self.input.attrs;
            let ident = &self.input.ident;
            let generics = &self.input.generics;
            quote! {
                #[derive(Clone, Copy, PartialEq, Eq, Hash)]
                #(#attributes)*
                #vis struct #ident #generics { op: ::pliron::context::Ptr<::pliron::operation::Operation> }
            }
        };

        let impl_op_trait = &self.impl_op;

        tokens.extend(quote! {
            #def_struct

            #impl_op_trait
        });
    }
}

struct ImplOp {
    struct_name: syn::Ident,
    dialect_name: String,
    op_name: String,
}

impl ToTokens for ImplOp {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        let name = &self.struct_name;
        let dialect = &self.dialect_name;
        let op_name = &self.op_name;
        tokens.extend(quote! {
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

                fn verify_interfaces(&self, ctx: &::pliron::context::Context) -> ::pliron::result::Result<()> {
                    if let Some(interface_verifiers) =
                        ::pliron::op::OP_INTERFACE_VERIFIERS_MAP.get(&Self::get_opid_static())
                    {
                        for (_, verifier) in interface_verifiers {
                            verifier(self, ctx)?;
                        }
                    }
                    Ok(())
                }
            }
        });
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use expect_test::expect;

    #[test]
    fn simple() {
        let arg = quote! { "testing.testop" };
        let input = quote! {
            struct TestOp;
        };
        let op = def_op(arg, input).unwrap();
        let f = syn::parse2::<syn::File>(op).unwrap();
        let got = prettyplease::unparse(&f);

        expect![[r##"
            #[derive(Clone, Copy, PartialEq, Eq, Hash)]
            #[derive(::pliron_derive::DeriveAttribAcceptor)]
            #[ir_kind = "op"]
            struct TestOp {
                op: ::pliron::context::Ptr<::pliron::operation::Operation>,
            }
            impl ::pliron::op::Op for TestOp {
                fn get_operation(&self) -> ::pliron::context::Ptr<::pliron::operation::Operation> {
                    self.op
                }
                fn wrap_operation(
                    op: ::pliron::context::Ptr<::pliron::operation::Operation>,
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
                fn verify_interfaces(
                    &self,
                    ctx: &::pliron::context::Context,
                ) -> ::pliron::result::Result<()> {
                    if let Some(interface_verifiers) = ::pliron::op::OP_INTERFACE_VERIFIERS_MAP
                        .get(&Self::get_opid_static())
                    {
                        for (_, verifier) in interface_verifiers {
                            verifier(self, ctx)?;
                        }
                    }
                    Ok(())
                }
            }
        "##]]
        .assert_eq(&got);
    }
}
