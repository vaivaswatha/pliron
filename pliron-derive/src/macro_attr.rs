use std::fmt;

use crate::irfmt::Format;
use syn::{Expr, ExprLit, Lit, Result};

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

impl IRKind {
    pub const ATTR_NAME: &'static str = "ir_kind";

    pub fn from_syn(attr: &syn::Attribute) -> Result<Self> {
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct IRFormat(pub Format);

impl IRFormat {
    pub const ATTR_NAME: &'static str = "ir_format";

    pub fn from_syn(attr: &syn::Attribute) -> Result<Self> {
        attr.meta.require_name_value()?;
        let value = attrib_lit_value(attr)?.value();
        Self::try_from(value).map_err(|e| syn::Error::new_spanned(attr, e))
    }
}

impl From<IRFormat> for Format {
    fn from(f: IRFormat) -> Self {
        f.0
    }
}

impl From<Format> for IRFormat {
    fn from(f: Format) -> Self {
        Self(f)
    }
}

impl TryFrom<String> for IRFormat {
    type Error = Box<dyn std::error::Error>;

    fn try_from(value: String) -> std::result::Result<Self, Self::Error> {
        let f = Format::parse(&value)?;
        Ok(Self(f))
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
