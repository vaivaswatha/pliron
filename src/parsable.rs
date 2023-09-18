//! IR objects that can be parsed from their text representation.

use crate::context::Context;
use combine::{
    easy,
    parser::char::spaces,
    stream::{
        self, buffered,
        position::{self, SourcePosition},
        IteratorStream,
    },
    ParseResult, Parser, Stream,
};

/// State during parsing of any [Parsable] object.
/// Every parser implemented using [Parsable] will be passed
/// a mutable reference (wrapped with [StateStream]) to this state.
pub struct State<'a> {
    pub ctx: &'a mut Context,
}

/// A wrapper around any [char] [Iterator] object.
/// Buffering and positioning are automatically handled hereafter.
pub struct CharIterator<'a>(Box<dyn Iterator<Item = char> + 'a>);

impl<'a> Iterator for CharIterator<'a> {
    type Item = char;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }
}

/// A [State]ful [Stream]. Every [Parsable::parser] gets this as input,
/// allowing for the parser to have access to a state.
pub type StateStream<'a> = stream::state::Stream<
    buffered::Stream<
        easy::Stream<
            stream::position::Stream<stream::IteratorStream<CharIterator<'a>>, SourcePosition>,
        >,
    >,
    State<'a>,
>;

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
///     { state_stream_from_iterator, StateStream, Parsable, State}
/// };
/// #[derive(PartialEq, Eq)]
/// struct Number { n: u64 }
/// impl Parsable for Number {
///     type Parsed = Number;
///     fn parse<'a>(
///         state_stream: &mut StateStream<'a>,
///     ) -> ParseResult<Self::Parsed, easy::ParseError<StateStream<'a>>> {
///         many1::<String, _, _>(digit())
///         .map(|digits| {
///             let _ : &mut Context = state_stream.state.ctx;
///             Number { n: digits.parse::<u64>().unwrap() }
///         })
///         .parse_stream(&mut state_stream.stream)
///     }
/// }
/// let mut ctx = Context::new();
/// let state_stream = state_stream_from_iterator("100".chars(), State { ctx: &mut ctx });
/// assert!(Number::parser().parse(state_stream).unwrap().0 == Number { n: 100 });
///
/// ```
pub trait Parsable {
    type Parsed;

    /// Define a parser using existing combinators and call
    /// [Parser::parse_stream] to get the final [ParseResult].
    /// Use [state_stream.state](StateStream::state) as necessary.
    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
    ) -> ParseResult<Self::Parsed, easy::ParseError<StateStream<'a>>>;

    /// Get a parser combinator that can work on [StateStream] as its input.
    fn parser<'a>(
    ) -> Box<dyn Parser<StateStream<'a>, Output = Self::Parsed, PartialState = ()> + 'a> {
        combine::parser(|parsable_state: &mut StateStream<'a>| {
            Self::parse(parsable_state).into_result()
        })
        .boxed()
    }

    /// Same as [Self::parser] but takes a unit reference for use as [ParserFn]
    fn parser_fn<'a>(
        _: &'a (),
    ) -> Box<dyn Parser<StateStream<'a>, Output = Self::Parsed, PartialState = ()> + 'a> {
        Self::parser()
    }
}

/// Build a [StateStream] from an iterator, for use with [Parsable].
pub fn state_stream_from_iterator<'a, T: Iterator<Item = char> + 'a>(
    input: T,
    state: State<'a>,
) -> StateStream<'a> {
    StateStream {
        stream: buffered::Stream::new(
            easy::Stream::from(position::Stream::with_positioner(
                IteratorStream::new(CharIterator(Box::new(input))),
                SourcePosition::default(),
            )),
            100,
        ),
        state,
    }
}

/// A storable parser function. This allows storing a function pointer
/// to a parser in a table, allowing for invoking it indirectly.
// (if we can get rid of the dummy parameter, we wouldn't need [Parsable::parser_fn]).
pub type ParserFn<Parsed> =
    for<'a> fn(
        _: &'a (),
    ) -> Box<dyn Parser<StateStream<'a>, Output = Parsed, PartialState = ()> + 'a>;

///  Parse an identifier.
pub fn parse_id<Input: Stream<Token = char>>() -> impl Parser<Input, Output = String> {
    use combine::{many, parser::char};
    char::letter()
        .and(many::<String, _, _>(char::alpha_num().or(char::char('_'))))
        .map(|(c, rest)| c.to_string() + &rest)
}

/// Parse from `parser`, ignoring whitespace(s) before and after.
pub fn spaced<Input: Stream<Token = char>, Output>(
    parser: impl Parser<Input, Output = Output>,
) -> impl Parser<Input, Output = Output> {
    combine::between(spaces(), spaces(), parser)
}
