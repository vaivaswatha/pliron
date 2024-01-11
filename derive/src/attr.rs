use std::fmt;

use syn::{Expr, ExprLit, Lit, Result};

use crate::asmfmt::Format;

pub(crate) trait Attribute
where
    Self: Sized,
{
    const ATTR_NAME: &'static str;

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

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DialectName(String);
impl_attribute_name!(DialectName, "dialect");

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TypeName(String);
impl_attribute_name!(TypeName, "type_name");

impl TypeName {
    pub fn from_syn_opt_dialect(attr: &syn::Attribute) -> syn::Result<(Option<DialectName>, Self)> {
        let (d, n) = opt_string_pair_from_syn(attr)?;
        Ok((d.map(Into::into), n.into()))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AttributeName(String);
impl_attribute_name!(AttributeName, "attr_name");

impl AttributeName {
    pub fn from_syn_opt_dialect(attr: &syn::Attribute) -> syn::Result<(Option<DialectName>, Self)> {
        let (d, n) = opt_string_pair_from_syn(attr)?;
        Ok((d.map(Into::into), n.into()))
    }
}

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

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AsmFormat(pub Format);

impl Attribute for AsmFormat {
    const ATTR_NAME: &'static str = "asm_format";

    fn from_syn(attr: &syn::Attribute) -> Result<Self> {
        attr.meta.require_name_value()?;
        let value = attrib_lit_value(attr)?.value();
        Self::try_from(value).map_err(|e| syn::Error::new_spanned(attr, e))
    }
}

impl From<Format> for AsmFormat {
    fn from(f: Format) -> Self {
        Self(f)
    }
}

impl TryFrom<String> for AsmFormat {
    type Error = Box<dyn std::error::Error>;

    fn try_from(value: String) -> std::result::Result<Self, Self::Error> {
        let f = Format::parse(&value)?;
        Ok(Self(f))
    }
}

impl AsmFormat {
    pub fn new() -> Self {
        Self(Format::default())
    }

    pub fn format(&self) -> &Format {
        &self.0
    }

    pub fn format_mut(&mut self) -> &mut Format {
        &mut self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum IRKind {
    Type,
    Attribute,
    Op,
}

impl IRKind {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::Type => "type",
            Self::Attribute => "attribute",
            Self::Op => "op",
        }
    }
}

impl Attribute for IRKind {
    const ATTR_NAME: &'static str = "ir_kind";

    fn from_syn(attr: &syn::Attribute) -> Result<Self> {
        attr.meta.require_name_value()?;
        let value = attrib_lit_value(attr)?.value();
        Self::try_from(value).map_err(|e| syn::Error::new_spanned(attr, e))
    }
}

impl TryFrom<String> for IRKind {
    type Error = String;

    fn try_from(value: String) -> std::result::Result<Self, Self::Error> {
        Self::try_from(value.as_str())
    }
}

impl<'a> TryFrom<&'a str> for IRKind {
    type Error = String;

    fn try_from(value: &'a str) -> std::result::Result<Self, Self::Error> {
        match value {
            "type" => Ok(Self::Type),
            "attribute" => Ok(Self::Attribute),
            "op" => Ok(Self::Op),
            _ => Err(format!("unknown IR kind: {}", value)),
        }
    }
}

impl fmt::Display for IRKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl quote::ToTokens for IRKind {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let value = self.as_str();
        quote::quote!(
            #[ir_kind = #value]
        )
        .to_tokens(tokens)
    }
}

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
