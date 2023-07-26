//! IR objects that can be parsed from their text representation.

use crate::context::Context;
use combine::{
    easy,
    stream::{
        self,
        position::{self, DefaultPositioned, Positioner},
    },
    ParseResult, Parser, Stream,
};

/// State during parsing of any [Parsable] object.
/// Every parser implemented using [Parsable] will be passed
/// a mutable reference (wrapped with [StateStream]) to this state.
pub struct State<'a> {
    pub ctx: &'a mut Context,
}

/// A [Stream] that can be wrapped with [easy::Stream].
// https://www.reddit.com/r/rust/comments/w3rtnl/confusion_about_trait_bounds_on_associated_types/
pub trait EasableStream:
    Stream<Token = char, Range = Self::RangeT, Position = Self::PositionT>
{
    type RangeT: PartialEq;
    type PositionT: Ord + Clone;
}

impl<T> EasableStream for T
where
    T: Stream<Token = char>,
    T::Range: PartialEq,
{
    type RangeT = T::Range;
    type PositionT = T::Position;
}

/// Combine [State] with [Stream]. Every [Parsable::parser] gets this as input,
/// thus allowing for the parser to have access to a state.
pub type StateStream<'a, S> = stream::state::Stream<easy::Stream<S>, State<'a>>;

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
/// use pliron::{context::Context, parsable::
///     { EasableStream, easy_positioned_state_stream, StateStream, Parsable, State}
/// };
/// #[derive(PartialEq, Eq)]
/// struct Number { n: u64 }
/// impl Parsable for Number {
///     type Parsed = Number;
///     fn parse<'a, S: EasableStream + 'a>(
///         state_stream: &mut StateStream<'a, S>,
///     ) -> ParseResult<Self::Parsed, easy::ParseError<S>> {
///         many1::<String, _, _>(digit())
///         .map(|digits| {
///             let _ : &mut Context = state_stream.state.ctx;
///             Number { n: digits.parse::<u64>().unwrap() }
///         })
///         .parse_stream(&mut state_stream.stream)
///     }
/// }
/// let mut ctx = Context::new();
/// let state_stream = easy_positioned_state_stream("100", State { ctx: &mut ctx });
/// assert!(Number::parser().parse(state_stream).unwrap().0 == Number { n: 100 });
///
/// ```
pub trait Parsable {
    type Parsed;

    /// Define a parser using existing combinators and call
    /// [Parser::parse_stream] on `state_stream.stream`
    /// to get the final [ParseResult].
    /// Use [StateStream::state] as necessary.
    fn parse<'a, S: EasableStream + 'a>(
        state_stream: &mut StateStream<'a, S>,
    ) -> ParseResult<Self::Parsed, easy::ParseError<S>>
    where
        Self: Sized;

    /// Get a parser combinator that can work on [StateStream] as its input.
    fn parser<'a, S: EasableStream + 'a>(
    ) -> Box<dyn Parser<StateStream<'a, S>, Output = Self::Parsed, PartialState = ()> + 'a>
    where
        Self: Sized,
    {
        combine::parser(|parsable_state: &mut StateStream<'a, S>| {
            Self::parse(parsable_state).into_result()
        })
        .boxed()
    }
}

/// Build a [StateStream] from suitable [Stream]s, for use with [Parsable].
pub fn easy_positioned_state_stream<S: EasableStream + DefaultPositioned>(
    stream: S,
    state: State<'_>,
) -> StateStream<'_, position::Stream<S, S::Positioner>>
where
    S::Positioner: Positioner<char>,
{
    StateStream {
        stream: easy::Stream::from(position::Stream::new(stream)),
        state,
    }
}

///  Parse an identifier.
pub fn parse_id<Input: Stream<Token = char>>() -> impl Parser<Input, Output = String> {
    use combine::{many, parser::char};
    char::letter()
        .and(many::<String, _, _>(char::alpha_num().or(char::char('_'))))
        .map(|(c, rest)| c.to_string() + &rest)
}
