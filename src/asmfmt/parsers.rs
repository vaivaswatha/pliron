use combine::{
    error::Commit,
    many1,
    parser::{
        char::{digit, spaces, string},
        choice::choice,
    },
    Parser, Stream,
};

use crate::{
    attribute::AttrId,
    context::Ptr,
    input_err,
    location::Located,
    parsable::{Parsable, ParseResult, StateStream},
    printable::Printable,
    r#type::{TypeId, TypeName, TypeObj},
};

pub trait AsmParser<'a, T> {
    fn parse_next(&self, state_stream: &mut StateStream<'a>) -> ParseResult<'a, T>;
}

impl<'a, T, F> AsmParser<'a, T> for F
where
    F: Fn(&mut StateStream<'a>) -> ParseResult<'a, T>,
{
    fn parse_next(&self, state_stream: &mut StateStream<'a>) -> ParseResult<'a, T> {
        self(state_stream)
    }
}

impl<'a> AsmParser<'a, &'a str> for &'static str {
    fn parse_next(&self, state_stream: &mut StateStream<'a>) -> ParseResult<'a, &'a str> {
        literal(self).parse_next(state_stream)
    }
}

pub struct ParseableParser<T>(std::marker::PhantomData<T>);

pub fn from_parseable<T>() -> ParseableParser<T> {
    ParseableParser(std::marker::PhantomData)
}

impl<'a> AsmParser<'a, bool> for bool {
    fn parse_next(&self, state_stream: &mut StateStream<'a>) -> ParseResult<'a, bool> {
        bool().parse_next(state_stream)
    }
}

impl<'a> AsmParser<'a, bool> for ParseableParser<bool> {
    fn parse_next(&self, state_stream: &mut StateStream<'a>) -> ParseResult<'a, bool> {
        bool().parse_next(state_stream)
    }
}

impl<'a> AsmParser<'a, u32> for ParseableParser<u32> {
    fn parse_next(&self, state_stream: &mut StateStream<'a>) -> ParseResult<'a, u32> {
        number::<u32>().parse_next(state_stream)
    }
}

impl<'a, T> AsmParser<'a, T> for ParseableParser<T>
where
    T: Parsable<Arg = (), Parsed = T>,
{
    fn parse_next(&self, state_stream: &mut StateStream<'a>) -> ParseResult<'a, T> {
        spaces().parse_stream(state_stream).into_result()?;
        T::parse(state_stream, ())
    }
}

pub fn type_name<'a>() -> impl AsmParser<'a, TypeName> {
    from_parseable()
}

pub fn type_id<'a>() -> impl AsmParser<'a, TypeId> {
    from_parseable()
}

pub fn type_header<'a>() -> impl AsmParser<'a, TypeId> {
    type_id()
}

pub fn attr_header<'a>() -> impl AsmParser<'a, AttrId> {
    from_parseable()
}

/// A parser combinator to parse [TypeId] followed by the type's contents.
pub fn type_parser<'a>(
) -> Box<dyn Parser<StateStream<'a>, Output = Ptr<TypeObj>, PartialState = ()> + 'a> {
    combine::parser(|parsable_state: &mut StateStream<'a>| type_parse(parsable_state)).boxed()
}

/// Parse an identified type, which is [TypeId] followed by its contents.
pub fn type_parse<'a>(state_stream: &mut StateStream<'a>) -> ParseResult<'a, Ptr<TypeObj>> {
    let loc = state_stream.loc();
    let type_id_parser = spaced(TypeId::parser(()));

    let mut type_parser = type_id_parser.then(move |type_id: TypeId| {
        // This clone is to satify the borrow checker.
        let loc = loc.clone();
        combine::parser(move |parsable_state: &mut StateStream<'a>| {
            let state = &parsable_state.state;
            let dialect = state
                .ctx
                .dialects
                .get(&type_id.dialect)
                .expect("Dialect name parsed but dialect isn't registered");
            let Some(type_parser) = dialect.types.get(&type_id) else {
                input_err!(loc.clone(), "Unregistered type {}", type_id.disp(state.ctx))?
            };
            type_parser(&(), ()).parse_stream(parsable_state).into()
        })
    });

    type_parser.parse_stream(state_stream).into_result()
}

/// Parse from `parser`, ignoring whitespace(s) before and after.
/// > **Warning**: Do not use this inside inside repeating combiners, such as [combine::many].
///     After successfully parsing one instance, if spaces are consumed to parse
///     the next one, but the next one doesn't exist, it is treated as a failure
///     that consumed some input. This messes things up. So spaces must be consumed
///     after a successfull parse, and not prior to an upcoming one.
///     A possibly right way to, for example, parse a comma separated list of [Identifier]s:
///
///```
///     # use combine::{parser::char::spaces, Parser};
///     # use pliron::parsable::Parsable;
///     let ids = spaces().with
///               (combine::sep_by::<Vec<_>, _, _, _>
///                 (pliron::identifier::Identifier::parser(()).skip(spaces()),
///                 combine::token(',').skip(spaces())));
///```
pub fn spaced<Input: Stream<Token = char>, Output>(
    parser: impl Parser<Input, Output = Output>,
) -> impl Parser<Input, Output = Output> {
    combine::between(spaces(), spaces(), parser)
}

pub fn literal<'a>(lit: &'static str) -> impl AsmParser<'a, &'a str> {
    move |state_stream: &mut StateStream<'a>| {
        spaces().parse_stream(state_stream).into_result()?;
        let x = string(lit).parse_stream(state_stream).into_result()?.0;
        Ok((x, Commit::Commit(())))
    }
}

pub fn bool<'a>() -> impl AsmParser<'a, bool> {
    move |state_stream: &mut StateStream<'a>| {
        spaces().parse_stream(state_stream).into_result()?;
        let x = choice((string("true"), string("false")))
            .parse_stream(state_stream)
            .into_result()?
            .0;
        Ok((x == "true", Commit::Commit(())))
    }
}

pub fn number<'a, T>() -> impl AsmParser<'a, T>
where
    T: std::fmt::Debug + std::str::FromStr,
    <T as std::str::FromStr>::Err: std::fmt::Debug,
{
    move |state_stream: &mut StateStream<'a>| {
        spaces().parse_stream(state_stream).into_result()?;
        many1::<String, _, _>(digit())
            .map(|s| s.parse::<T>().unwrap())
            .parse_stream(state_stream)
            .into_result()
    }
}

#[cfg(test)]
mod test {
    use expect_test::expect;

    use crate::{
        asmfmt::parsers::type_parser,
        context::Context,
        dialects, location,
        parsable::{self, state_stream_from_iterator},
    };

    #[test]
    fn test_parse_type() {
        let mut ctx = Context::new();
        dialects::builtin::register(&mut ctx);

        let state_stream = state_stream_from_iterator(
            "builtin.some".chars(),
            parsable::State::new(&mut ctx, location::Source::InMemory),
        );

        let res = type_parser().parse(state_stream);
        let err_msg = format!("{}", res.err().unwrap());

        let expected_err_msg = expect![[r#"
            Parse error at line: 1, column: 1
            Unregistered type builtin.some
        "#]];
        expected_err_msg.assert_eq(&err_msg);

        let state_stream = state_stream_from_iterator(
            "builtin.int a".chars(),
            parsable::State::new(&mut ctx, location::Source::InMemory),
        );

        let res = type_parser().parse(state_stream);
        let err_msg = format!("{}", res.err().unwrap());

        let expected_err_msg = expect![[r#"
            Parse error at line: 1, column: 13
            Unexpected `a`
            Expected `<`
        "#]];
        expected_err_msg.assert_eq(&err_msg);

        let state_stream = state_stream_from_iterator(
            "builtin.int <si32>".chars(),
            parsable::State::new(&mut ctx, location::Source::InMemory),
        );

        let parsed = type_parser().parse(state_stream).unwrap().0;
        assert_eq!(
            crate::printable::Printable::disp(&parsed, &ctx).to_string(),
            "builtin.int <si32>"
        );
    }
}
