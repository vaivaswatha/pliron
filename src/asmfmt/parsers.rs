use combine::{
    error::Commit,
    many1,
    parser::{
        char::{digit, spaces, string},
        choice::choice,
    },
    Parser,
};

use crate::{
    attribute::AttrId,
    parsable::{Parsable, ParseResult, StateStream},
    r#type::{TypeId, TypeName},
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
