//! IR objects that can be parsed from their text representation.

use crate::context::Context;
use combine::{ParseResult, Parser, Stream};

/// State during parsing of any [Parsable] object.
/// Every parser implemented using [Parsable] will be passed
/// a mutable reference to this state.
pub struct State<'a> {
    pub ctx: &'a mut Context,
}

pub type StateStream<'a, Input> = combine::stream::state::Stream<Input, State<'a>>;

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
/// use pliron::{context::Context, parsable::{StateStream, Parsable, State}};
/// #[derive(PartialEq, Eq)]
/// struct Number { n: u64 }
/// impl Parsable for Number {
///     type Parsed = Number;
///     fn parse<'a, Input: Stream<Token = char> + 'a>(
///         state_stream: &mut StateStream<Input>,
///     ) -> ParseResult<Self::Parsed, Input::Error> {
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

    /// Don't be scared by the signature. Just copy it and use
    /// [Parser::parse_stream] to parse the input stream.
    /// Use [Context] as necessary.
    fn parse<'a, Input: Stream<Token = char> + 'a>(
        state_stream: &mut StateStream<Input>,
    ) -> ParseResult<Self::Parsed, Input::Error>
    where
        Self: Sized;

    /// Get a parser combinator that can work on [StateStream] as its input.
    fn parser<'a, Input: Stream<Token = char> + 'a>(
    ) -> Box<dyn Parser<StateStream<'a, Input>, Output = Self::Parsed, PartialState = ()> + 'a>
    where
        Self: Sized,
    {
        combine::parser(|parsable_state: &mut StateStream<Input>| {
            Self::parse(parsable_state).into_result()
        })
        .boxed()
    }
}
