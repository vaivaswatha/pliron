//! Utility traits such as [Named], [Verify] etc.

use combine::{ParseResult, Parser, Stream};

use crate::{context::Context, error::CompilerError};

/// Check and ensure correctness.
pub trait Verify {
    fn verify(&self, ctx: &Context) -> Result<(), CompilerError>;
}

/// Anything that has a name.
pub trait Named {
    fn get_name(&self, ctx: &Context) -> String;
}

/// For types that contain a reference-counted container,
/// provides methods to [share](Self::share) (i.e., [Rc::clone](std::rc::Rc::clone))
/// and [deep copy](Self::replicate) inner data.
/// This just avoids ambiguity over using `Rc::clone`, which doesn't clone
/// inner data but increases the reference count.
pub trait RcSharable {
    /// Light weight (reference counted) clone.
    fn share(&self) -> Self;

    /// New copy that doesn't share the internal state of self.
    fn replicate(&self) -> Self;
}

pub type ParsableState<'a, Input> = combine::stream::state::Stream<Input, &'a mut Context>;

/// Any object that can be parsed from its [Printable](crate::printable::Printable) text.
///
/// Implement [parse](Parsable::parse) and call [get_parser](Parsable::get_parser)
/// to get a parser combinator that can be combined with any other parser
/// from the [combine] library.
/// Example:
/// ```
/// use combine::{
///     Parser, Stream, easy, stream::position,
///     parser::char::digit, many1, ParseResult
/// };
/// use pliron::{context::Context, common_traits::{ParsableState, Parsable}};
/// #[derive(PartialEq, Eq)]
/// struct Number { n: u64 }
/// impl Parsable for Number {
///     type Parsed = Number;
///     fn parse<'a, Input: Stream<Token = char> + 'a>(
///         parsable_state: &mut ParsableState<Input>,
///     ) -> ParseResult<Self::Parsed, Input::Error> {
///         many1::<String, _, _>(digit())
///         .map(|digits| {
///             let _ : &mut Context = parsable_state.state;
///             Number { n: digits.parse::<u64>().unwrap() }
///         })
///         .parse_stream(&mut parsable_state.stream)
///     }
/// }
/// let mut ctx = Context::new();
/// let input_stream = easy::Stream::from(position::Stream::new("100"));
/// let input_state = ParsableState {
///     stream: input_stream,
///     state: &mut ctx,
/// };
/// assert!(Number::get_parser().parse(input_state).unwrap().0 == Number { n: 100 });
///
/// ```
pub trait Parsable {
    type Parsed;

    /// Don't be scared by the signature. Just copy it and use
    /// [Parser::parse_stream] to parse the input stream.
    /// Use [Context] as necessary.
    fn parse<'a, Input: Stream<Token = char> + 'a>(
        parsable_state: &mut ParsableState<Input>,
    ) -> ParseResult<Self::Parsed, Input::Error>
    where
        Self: Sized;

    /// Get a parser combinator that can work on [ParsableState] as its input.
    fn get_parser<'a, Input: Stream<Token = char> + 'a>(
    ) -> Box<dyn Parser<ParsableState<'a, Input>, Output = Self::Parsed, PartialState = ()> + 'a>
    where
        Self: Sized,
    {
        combine::parser(|parsable_state: &mut ParsableState<Input>| {
            Self::parse(parsable_state).into_result()
        })
        .boxed()
    }
}
