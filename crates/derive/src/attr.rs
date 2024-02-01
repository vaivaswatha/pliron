//! Support for parsing and validating common attributes used by the different derive macros.

use std::fmt;

use syn::{Expr, ExprLit, Lit, Result};

// Common trait all attributes should implement.
pub(crate) trait Attribute
where
    Self: Sized,
{
    /// The attribute name. In the users source code it will look similar to
    /// `#[attribute_name = ...]` or `#[attribute_name(...)]`.
    ///
    /// We make no assumptions about the attribute style here.
    const ATTR_NAME: &'static str;

    /// Parse and validate the attribute value.
    fn from_syn(attr: &syn::Attribute) -> Result<Self>;
}

macro_rules! impl_attribute_name {
    ($ty:ident, $name:expr) => {
        impl Attribute for $ty {
            const ATTR_NAME: &'static str = $name;

            fn from_syn(attr: &syn::Attribute) -> Result<Self> {
                attr.meta.require_name_value()?;
                let value = attrib_lit_value(attr)?.value();
                Ok(Self(value))
            }
        }

        impl From<&str> for $ty {
            fn from(s: &str) -> Self {
                Self(s.to_string())
            }
        }

        impl From<String> for $ty {
            fn from(s: String) -> Self {
                Self(s)
            }
        }

        impl fmt::Display for $ty {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "{}", self.0)?;
                Ok(())
            }
        }

        impl quote::ToTokens for $ty {
            fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
                self.0.to_tokens(tokens)
            }
        }
    };
}

/// The `#[dialect = ...]` attribute.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DialectName(String);
impl_attribute_name!(DialectName, "dialect");

/// The `#[type_name = ...]` attribute.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TypeName(String);
impl_attribute_name!(TypeName, "type_name");

impl TypeName {
    pub fn from_syn_opt_dialect(attr: &syn::Attribute) -> syn::Result<(Option<DialectName>, Self)> {
        let (d, n) = opt_string_pair_from_syn(attr)?;
        Ok((d.map(Into::into), n.into()))
    }
}

/// The `#[attr_name = ...]` attribute.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AttributeName(String);
impl_attribute_name!(AttributeName, "attr_name");

impl AttributeName {
    pub fn from_syn_opt_dialect(attr: &syn::Attribute) -> syn::Result<(Option<DialectName>, Self)> {
        let (d, n) = opt_string_pair_from_syn(attr)?;
        Ok((d.map(Into::into), n.into()))
    }
}

/// The `#[op_name = ...]` attribute.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct OpName(String);
impl_attribute_name!(OpName, "op_name");

impl OpName {
    pub fn from_syn_opt_dialect(attr: &syn::Attribute) -> syn::Result<(Option<DialectName>, Self)> {
        let (d, n) = opt_string_pair_from_syn(attr)?;
        Ok((d.map(Into::into), n.into()))
    }
}

fn opt_string_pair_from_syn(attr: &syn::Attribute) -> syn::Result<(Option<String>, String)> {
    attr.meta.require_name_value()?;
    let value = attrib_lit_value(attr)?.value();
    match value.split_once('.') {
        Some((d, n)) => Ok((Some(d.to_string()), n.to_string())),
        None => Ok((None, value)),
    }
}

/// Helper to check that an attribute is not already set in `value`.
/// The helper ensures consistent reporting of errors.
pub(crate) fn require_once<T>(
    attr_name: &str,
    value: &Option<T>,
    attr: &syn::Attribute,
) -> syn::Result<()> {
    if value.is_some() {
        Err(syn::Error::new_spanned(
            attr,
            format!("{} attribute can only be applied once", attr_name),
        ))
    } else {
        Ok(())
    }
}

/// Read the value of an name value style attribute.
///
/// For example read the value `bar` from the `foo` attribute: `#[foo = "bar"]`.
///
/// Returns an error if an alterantive attribute style is used.
pub(crate) fn attrib_lit_value(attr: &syn::Attribute) -> syn::Result<&syn::LitStr> {
    let nv = attr.meta.require_name_value()?;
    let Expr::Lit(ExprLit {
        lit: Lit::Str(ref lit),
        ..
    }) = nv.value
    else {
        return Err(syn::Error::new_spanned(
            nv,
            format!(
                "expected {} attribute to be a string literal",
                attr.path().get_ident().unwrap()
            ),
        ));
    };
    Ok(lit)
}
