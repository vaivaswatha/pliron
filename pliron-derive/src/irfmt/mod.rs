use proc_macro2::TokenStream;
use quote::format_ident;
use syn::parse::{Parse, ParseStream};
use syn::Data;
use syn::{self, DataStruct, DeriveInput};

mod eval;
mod parser;

pub use eval::AttribTypeFmtEvaler;

use crate::macro_attr::{require_once, IRFormat, IRKind};

/// Represents the common input to derive macros that use the `ir_format` attribute in conjunction
/// with the struct definition in order to create parsers, printers for an IR entity.
pub(crate) struct IRFmtInput {
    pub ident: syn::Ident,
    pub kind: IRKind,
    pub data: FmtData,
    pub format: Format,
}

pub(crate) enum FmtData {
    Struct(Struct),
}

impl Parse for IRFmtInput {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let input = DeriveInput::parse(input)?;
        Self::try_from(input)
    }
}

impl TryFrom<DeriveInput> for IRFmtInput {
    type Error = syn::Error;

    fn try_from(input: DeriveInput) -> syn::Result<Self> {
        let mut kind = None;
        let mut format = None;

        for attr in &input.attrs {
            if attr.path().is_ident(IRFormat::ATTR_NAME) {
                require_once(IRFormat::ATTR_NAME, &format, attr)?;
                format = Some(IRFormat::from_syn(attr)?);
            }
            if attr.path().is_ident(IRKind::ATTR_NAME) {
                require_once(IRKind::ATTR_NAME, &kind, attr)?;
                kind = Some(IRKind::from_syn(attr)?);
            }
        }

        let Some(kind) = kind else {
            return Err(syn::Error::new_spanned(
                input,
                "unknown IR object type. Use #[ir_kind=...] or one of the supported derive clauses Type, Attrib, ...",
            ));
        };

        let data = match input.data {
            Data::Struct(ref data) => Struct::from_syn(data).map(FmtData::Struct),
            Data::Enum(_) => Err(syn::Error::new_spanned(
                &input,
                "Type can only be derived for structs",
            )),
            Data::Union(_) => Err(syn::Error::new_spanned(
                &input,
                "Type can only be derived for structs",
            )),
        }?;

        let format = match format {
            Some(f) => f,
            None => {
                let mut format = match kind {
                    IRKind::Op => generic_op_format(),
                    IRKind::Type | IRKind::Attribute => try_format_from_input(&input)?,
                };
                if !format.is_empty() && kind != IRKind::Op {
                    format.enclose(Elem::Lit("<".into()), Elem::Lit(">".into()));
                }
                format.into()
            }
        };

        let mut format: Format = format.into();
        if kind == IRKind::Op {
            format.prepend(Optional::new(
                Elem::new_directive("results"),
                Format::from(vec![Elem::new_directive("results"), Elem::new_lit(" = ")]),
            ));
        }

        Ok(Self {
            ident: input.ident,
            kind,
            format,
            data,
        })
    }
}

/// Struct format data.
pub(crate) struct Struct {
    pub fields: Vec<FieldIdent>,
}

impl Struct {
    fn from_syn(data: &DataStruct) -> syn::Result<Self> {
        let fields = data
            .fields
            .iter()
            .enumerate()
            .map(|(i, f)| match f.ident {
                Some(ref ident) => FieldIdent::Named(ident.to_string()),
                None => FieldIdent::Unnamed(i),
            })
            .collect();

        Ok(Self { fields })
    }
}

/// Field identifier of an IR entity that can be used a variable in a format string.
/// We extract struct fields as field identifiers.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum FieldIdent {
    Named(String),
    Unnamed(usize),
}

impl From<FieldIdent> for Elem {
    fn from(value: FieldIdent) -> Self {
        match value {
            FieldIdent::Named(name) => Elem::new_var(name),
            FieldIdent::Unnamed(index) => Elem::new_unnamed_var(index),
        }
    }
}

impl From<&FieldIdent> for Elem {
    fn from(value: &FieldIdent) -> Self {
        match value {
            FieldIdent::Named(name) => Elem::new_var(name),
            FieldIdent::Unnamed(index) => Elem::new_unnamed_var(*index),
        }
    }
}

impl From<&str> for FieldIdent {
    fn from(s: &str) -> Self {
        Self::Named(s.to_string())
    }
}

impl From<String> for FieldIdent {
    fn from(s: String) -> Self {
        Self::Named(s)
    }
}

impl From<usize> for FieldIdent {
    fn from(i: usize) -> Self {
        Self::Unnamed(i)
    }
}

impl quote::ToTokens for FieldIdent {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            Self::Named(name) => {
                let ident = format_ident!("{}", name);
                ident.to_tokens(tokens);
            }
            Self::Unnamed(index) => {
                let ident = syn::Index::from(*index);
                ident.to_tokens(tokens);
            }
        }
    }
}

/// A parsed format string.
///
/// The format string is a sequence of literals, variables, and directives.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub(crate) struct Format {
    pub elems: Vec<Elem>,
}

impl From<Vec<Elem>> for Format {
    fn from(elems: Vec<Elem>) -> Self {
        Self { elems }
    }
}

impl Format {
    pub fn is_empty(&self) -> bool {
        self.elems.is_empty()
    }

    pub fn prepend(&mut self, elem: impl Into<Elem>) {
        self.elems.insert(0, elem.into());
    }

    pub fn append(&mut self, elem: impl Into<Elem>) {
        self.elems.push(elem.into());
    }

    pub fn enclose(&mut self, open: impl Into<Elem>, close: impl Into<Elem>) {
        self.prepend(open);
        self.append(close);
    }
}

impl Format {
    /// Parse a format string.
    pub fn parse(input: &str) -> parser::Result<Self> {
        parser::parse(input)
    }
}

/// A single element term in a format string.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Elem {
    /// Literal is a custom string enclosed in backticks. For example `lit` or `(`.
    Lit(Lit),

    /// varialbes are custom identifiers starting with a dollar sign. For example $var or $0.
    Var(Var),

    /// Unnamed variables are custom identifiers starting with a dollar sign and a number.
    UnnamedVar(UnnamedVar),

    /// Directives are builtin identifiers. Some directives may have optional arguments enclosed
    // in parens. For example `attr-dict` or `directive($arg1, other-directive)`.
    Directive(Directive),

    /// Optional represents an optional format string.
    Optional(Optional),
}

impl Default for Elem {
    fn default() -> Self {
        Self::Lit(Lit::new(""))
    }
}

impl Elem {
    pub fn new_lit(s: impl Into<String>) -> Self {
        Self::Lit(Lit::new(s))
    }

    pub fn new_lit_at(pos: usize, s: impl Into<String>) -> Self {
        Self::Lit(Lit::new_at(pos, s))
    }

    pub fn new_var(s: impl Into<String>) -> Self {
        Self::Var(Var::new(s))
    }

    pub fn new_var_at(pos: usize, s: impl Into<String>) -> Self {
        Self::Var(Var::new_at(pos, s.into()))
    }

    pub fn new_unnamed_var(index: usize) -> Self {
        Self::UnnamedVar(UnnamedVar::new(index))
    }

    pub fn new_unnamed_var_at(pos: usize, index: usize) -> Self {
        Self::UnnamedVar(UnnamedVar::new_at(pos, index))
    }

    pub fn new_directive(name: impl Into<String>) -> Self {
        Self::Directive(Directive::new(name))
    }

    #[allow(dead_code)] // used in tests.
    pub fn new_directive_at(pos: usize, name: impl Into<String>) -> Self {
        Self::Directive(Directive::new_at(pos, name))
    }

    #[allow(dead_code)]
    pub fn new_directive_with_args(name: impl Into<String>, args: Vec<Elem>) -> Self {
        Self::Directive(Directive::new_with_args(name, args))
    }

    pub fn new_directive_with_args_at(
        pos: usize,
        name: impl Into<String>,
        args: Vec<Elem>,
    ) -> Self {
        Self::Directive(Directive::new_with_args_at(pos, name, args))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Lit {
    pub pos: Option<usize>,
    pub lit: String,
}

impl From<Lit> for Elem {
    fn from(lit: Lit) -> Self {
        Self::Lit(lit)
    }
}

impl From<&str> for Lit {
    fn from(s: &str) -> Self {
        Self::new(s)
    }
}

impl Lit {
    pub fn new(s: impl Into<String>) -> Self {
        Self {
            pos: None,
            lit: s.into(),
        }
    }

    pub fn new_at(pos: usize, s: impl Into<String>) -> Self {
        Self {
            pos: Some(pos),
            lit: s.into(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Var {
    pub pos: Option<usize>,
    pub name: String,
}

impl Var {
    pub fn new(s: impl Into<String>) -> Self {
        Self {
            pos: None,
            name: s.into(),
        }
    }

    pub fn new_at(pos: usize, s: impl Into<String>) -> Self {
        Self {
            pos: Some(pos),
            name: s.into(),
        }
    }
}

impl From<Var> for Elem {
    fn from(lit: Var) -> Self {
        Self::Var(lit)
    }
}

impl From<&str> for Var {
    fn from(s: &str) -> Self {
        Self::new(s)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnnamedVar {
    pub pos: Option<usize>,
    pub index: usize,
}

impl From<UnnamedVar> for Elem {
    fn from(var: UnnamedVar) -> Self {
        Self::UnnamedVar(var)
    }
}

impl From<usize> for UnnamedVar {
    fn from(index: usize) -> Self {
        Self::new(index)
    }
}

impl UnnamedVar {
    pub fn new(index: usize) -> Self {
        Self { pos: None, index }
    }

    pub fn new_at(pos: usize, index: usize) -> Self {
        Self {
            pos: Some(pos),
            index,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Directive {
    pub pos: Option<usize>,
    pub name: String,
    pub args: Vec<Elem>,
}

impl Directive {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            pos: None,
            name: name.into(),
            args: vec![],
        }
    }

    pub fn new_at(pos: usize, name: impl Into<String>) -> Self {
        Self {
            pos: Some(pos),
            name: name.into(),
            args: vec![],
        }
    }

    pub fn new_with_args(name: impl Into<String>, args: Vec<Elem>) -> Self {
        Self {
            pos: None,
            name: name.into(),
            args,
        }
    }

    pub fn new_with_args_at(pos: usize, name: impl Into<String>, args: Vec<Elem>) -> Self {
        Self {
            pos: Some(pos),
            name: name.into(),
            args,
        }
    }
}

impl From<Directive> for Elem {
    fn from(directive: Directive) -> Self {
        Self::Directive(directive)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Optional {
    pub check: Box<Elem>,
    pub then_format: Format,
    pub else_format: Option<Format>,
}

impl From<Optional> for Elem {
    fn from(optional: Optional) -> Self {
        Self::Optional(optional)
    }
}

impl Optional {
    pub fn new(check: Elem, then_format: Format) -> Self {
        Self {
            check: Box::new(check),
            then_format,
            else_format: None,
        }
    }

    #[allow(dead_code)]
    pub fn new_with_else(check: Elem, then_format: Format, else_format: Format) -> Self {
        Self {
            check: Box::new(check),
            then_format,
            else_format: Some(else_format),
        }
    }
}

struct FmtValue(Vec<Elem>);

impl From<Elem> for FmtValue {
    fn from(elem: Elem) -> Self {
        Self(vec![elem])
    }
}

impl From<Vec<Elem>> for FmtValue {
    fn from(elems: Vec<Elem>) -> Self {
        Self(elems)
    }
}

impl From<Directive> for FmtValue {
    fn from(d: Directive) -> Self {
        Self(vec![Elem::Directive(d)])
    }
}

impl From<Optional> for FmtValue {
    fn from(opt: Optional) -> Self {
        Self(vec![Elem::Optional(opt)])
    }
}

impl From<FmtValue> for Vec<Elem> {
    fn from(value: FmtValue) -> Self {
        value.0
    }
}

impl From<FmtValue> for Format {
    fn from(value: FmtValue) -> Self {
        Self { elems: value.0 }
    }
}

impl FmtValue {
    // flattens a FmtValue such that it contains no nested Values.
    fn flatten(self) -> Vec<Elem> {
        self.0
    }

    fn flatten_into(self, values: &mut Vec<Elem>) {
        values.extend(self.0);
    }
}

pub(crate) fn generic_op_format() -> Format {
    Format {
        elems: vec![Directive::new("operation_generic_format").into()],
    }
}

pub(crate) fn try_format_from_input(input: &syn::DeriveInput) -> syn::Result<Format> {
    // TODO: add support for per field attributes?

    let data = match input.data {
        Data::Struct(ref data) => data,
        _ => {
            return Err(syn::Error::new_spanned(
                input,
                "Type can only be derived for structs",
            ))
        }
    };

    let elems = match data.fields {
        syn::Fields::Named(ref fields) => {
            let mut elems = vec![];
            for (i, field) in fields.named.iter().enumerate() {
                let ident = field.ident.as_ref().unwrap();
                if i > 0 {
                    elems.push(Elem::new_lit(", "));
                }
                elems.push(Elem::new_lit(format!("{}=", ident)));
                elems.push(Elem::new_var(ident.to_string()));
            }
            elems
        }
        syn::Fields::Unnamed(ref fields) => (0..(fields.unnamed.len()))
            .map(Elem::new_unnamed_var)
            .collect::<Vec<_>>(),
        syn::Fields::Unit => vec![],
    };
    Ok(Format { elems })
}
