//! IR objects that can be parsed from their text representation.

use crate::context::Context;
use combine::{
    easy,
    stream::{self, position::SourcePosition},
    ParseResult, Parser, Stream,
};

/// State during parsing of any [Parsable] object.
/// Every parser implemented using [Parsable] will be passed
/// a mutable reference to this state.
pub struct State<'a> {
    pub ctx: &'a mut Context,
}

/// The kind of [combine::stream::Stream]s that we allow for [Parsable].
pub type ParsableStream<'a> = easy::Stream<stream::position::Stream<&'a str, SourcePosition>>;

/// Combines [State] with [ParsableStream].
pub type StateStream<'a> = stream::state::Stream<ParsableStream<'a>, State<'a>>;

/// Any object that can be parsed from its [Printable](crate::printable::Printable) text.
///
/// Implement [parse](Parsable::parse) and call [parser](Parsable::parser)
/// to get a parser combinator that can be combined with any other parser
/// from the [combine] library.
/// Example:
/// ```
/// use combine::{
///     Parser, Stream, easy, stream::position,
///     parser::char::digit, many1, ParseResult
/// };
/// use pliron::{context::Context, parsable::{ParsableStream, StateStream, Parsable, State}};
/// #[derive(PartialEq, Eq)]
/// struct Number { n: u64 }
/// impl Parsable for Number {
///     type Parsed = Number;
///     fn parse<'a>(
///         state_stream: &mut StateStream<'a>,
///     ) -> ParseResult<Self::Parsed, easy::ParseError<ParsableStream<'a>>> {
///         many1::<String, _, _>(digit())
///         .map(|digits| {
///             let _ : &mut Context = state_stream.state.ctx;
///             Number { n: digits.parse::<u64>().unwrap() }
///         })
///         .parse_stream(&mut state_stream.stream)
///     }
/// }
/// let mut ctx = Context::new();
/// let input_stream = easy::Stream::from(position::Stream::new("100"));
/// let input_state = StateStream {
///     stream: input_stream,
///     state: State { ctx: &mut ctx },
/// };
/// assert!(Number::parser().parse(input_state).unwrap().0 == Number { n: 100 });
///
/// ```
pub trait Parsable {
    type Parsed;

    /// Define a parser using existing combinators and call
    /// [Parser::parse_stream] on `state_stream.stream`
    /// to get the final [ParseResult].
    /// Use [StateStream::state] as necessary.
    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
    ) -> ParseResult<Self::Parsed, easy::ParseError<ParsableStream<'a>>>
    where
        Self: Sized;

    /// Get a parser combinator that can work on [StateStream] as its input.
    fn parser<'a>(
    ) -> Box<dyn Parser<StateStream<'a>, Output = Self::Parsed, PartialState = ()> + 'a>
    where
        Self: Sized,
    {
        combine::parser(|parsable_state: &mut StateStream<'a>| {
            Self::parse(parsable_state).into_result()
        })
        .boxed()
    }
}

///  Parse an identifier.
pub fn parse_id<Input: Stream<Token = char>>() -> impl Parser<Input, Output = String> {
    use combine::{many, parser::char};
    char::letter()
        .and(many::<String, _, _>(char::alpha_num().or(char::char('_'))))
        .map(|(c, rest)| c.to_string() + &rest)
}
