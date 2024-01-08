//! [Dialect]s are a mechanism to group related [Op](crate::op::Op)s, [Type](crate::type::Type)s
//! and [Attribute](crate::attribute::Attribute)s.
use std::{fmt::Display, ops::Deref};

use combine::Parser;
use rustc_hash::FxHashMap;

use crate::{
    attribute::{AttrId, AttrObj},
    context::{Context, Ptr},
    identifier::Identifier,
    input_err,
    location::{Located, Location},
    op::{OpId, OpObj},
    parsable::{IntoParseResult, Parsable, ParseResult, ParserFn, StateStream},
    printable::{self, Printable},
    r#type::{TypeId, TypeObj},
};

/// Dialect name: Safe wrapper around a String.
#[derive(Clone, Hash, PartialEq, Eq)]
pub struct DialectName(Identifier);

impl DialectName {
    /// Create a new DialectName
    pub fn new(name: &str) -> DialectName {
        DialectName(name.into())
    }
}

impl Printable for DialectName {
    fn fmt(
        &self,
        _ctx: &Context,
        _state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        <Self as Display>::fmt(self, f)
    }
}

impl Display for DialectName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Parsable for DialectName {
    type Arg = ();
    type Parsed = DialectName;

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed>
    where
        Self: Sized,
    {
        let loc = state_stream.loc();
        let id = Identifier::parser(());
        let mut parser = id.then(move |dialect_name| {
            let loc = loc.clone();
            combine::parser(move |state_stream: &mut StateStream<'a>| {
                let dialect_name = DialectName::new(&dialect_name);
                if state_stream.state.ctx.dialects.contains_key(&dialect_name) {
                    Ok(dialect_name).into_parse_result()
                } else {
                    input_err!(loc.clone(), "Unregistered dialect {}", *dialect_name)?
                }
            })
        });
        parser.parse_stream(state_stream).into()
    }
}

impl Deref for DialectName {
    type Target = String;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// A collection of Types and Ops.
/// Dialects are identified by their names.
pub struct Dialect {
    /// Name of this dialect.
    pub name: DialectName,
    /// Ops that are part of this dialect.
    pub ops: FxHashMap<OpId, ParserFn<Vec<(Identifier, Location)>, OpObj>>,
    /// Types that are part of this dialect.
    pub types: FxHashMap<TypeId, ParserFn<(), Ptr<TypeObj>>>,
    /// Attributes that are part of this dialect.
    pub attributes: FxHashMap<AttrId, ParserFn<(), AttrObj>>,
}

impl Printable for Dialect {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        write!(f, "{}", self.name.disp(ctx))
    }
}

impl Dialect {
    /// Create a new unregistered dialect.
    pub fn new(name: DialectName) -> Dialect {
        Dialect {
            name,
            ops: FxHashMap::default(),
            types: FxHashMap::default(),
            attributes: FxHashMap::default(),
        }
    }

    /// Register this dialect if not already registered.
    pub fn register(self, ctx: &mut Context) {
        ctx.dialects.entry(self.name.clone()).or_insert(self);
    }

    /// Add an [Op](crate::op::Op) to this dialect.
    pub fn add_op(&mut self, op: OpId, op_parser: ParserFn<Vec<(Identifier, Location)>, OpObj>) {
        assert!(op.dialect == self.name);
        self.ops.insert(op, op_parser);
    }

    /// Add a [Type](crate::type::Type) to this dialect.
    pub fn add_type(&mut self, ty: TypeId, ty_parser: ParserFn<(), Ptr<TypeObj>>) {
        assert!(ty.dialect == self.name);
        self.types.insert(ty, ty_parser);
    }

    /// Add an [Attribute](crate::attribute::Attribute) to this dialect.
    pub fn add_attr(&mut self, attr: AttrId, attr_parser: ParserFn<(), AttrObj>) {
        assert!(attr.dialect == self.name);
        self.attributes.insert(attr, attr_parser);
    }

    /// This Dialect's name.
    pub fn get_name(&self) -> &DialectName {
        &self.name
    }

    /// Get reference to a registered Dialect by name.
    pub fn get_ref(ctx: &Context, name: DialectName) -> Option<&Dialect> {
        ctx.dialects.get(&name)
    }

    /// Get mutable reference to a registered Dialect by name.
    pub fn get_mut(ctx: &mut Context, name: DialectName) -> Option<&mut Dialect> {
        ctx.dialects.get_mut(&name)
    }
}

#[cfg(test)]
mod test {

    use expect_test::expect;

    use crate::{
        context::Context,
        dialects, location,
        parsable::{self, state_stream_from_iterator, Parsable},
        printable::Printable,
    };

    use super::DialectName;

    #[test]
    fn parse_dialect_name() {
        let mut ctx = Context::new();
        dialects::builtin::register(&mut ctx);

        let state_stream = state_stream_from_iterator(
            "non_existant".chars(),
            parsable::State::new(&mut ctx, location::Source::InMemory),
        );

        let res = DialectName::parser(()).parse(state_stream);
        let err_msg = format!("{}", res.err().unwrap());

        let expected_err_msg = expect![[r#"
            Parse error at line: 1, column: 1
            Unregistered dialect non_existant
        "#]];
        expected_err_msg.assert_eq(&err_msg);

        let state_stream = state_stream_from_iterator(
            "builtin".chars(),
            parsable::State::new(&mut ctx, location::Source::InMemory),
        );

        let parsed = DialectName::parser(()).parse(state_stream).unwrap().0;
        assert_eq!(parsed.disp(&ctx).to_string(), "builtin");
    }
}
