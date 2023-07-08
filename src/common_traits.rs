//! Utility traits such as [DisplayWithContext], [Verify] etc.

use core::fmt;

use combine::{ParseResult, Parser, Stream};

use crate::{
    context::Context,
    error::CompilerError,
    with_context::{AttachContext, IterWithContext, WithContext},
};

// Traits for Display and Debug but with a paired Context.

///  Same as [fmt::Display], but with a [Context]. Example usage:
/// ```
/// use pliron::{with_context::*, common_traits::DisplayWithContext, context::Context};
/// use std::fmt;
/// struct S {
///     i: i64,
/// }
/// impl AttachContext for S {}
/// impl DisplayWithContext for S {
///     fn fmt(&self, _ctx: &Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
///         write!(f, "{}", self.i)
///     }
/// }
///
/// let ctx = Context::new();
/// assert!(S { i: 108 }.with_ctx(&ctx).to_string() == "108");
/// ```
pub trait DisplayWithContext: AttachContext {
    fn fmt(&self, ctx: &Context, f: &mut fmt::Formatter<'_>) -> fmt::Result;
}

impl<T: DisplayWithContext> fmt::Display for WithContext<'_, '_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.t.fmt(self.ctx, f)
    }
}

/// Same as [fmt::Debug], but with a [Context]. Example usage:
/// ```
/// use pliron::{with_context::*, common_traits::DebugWithContext, context::Context};
/// use std::fmt;
/// struct S {
///     i: i64,
/// }
/// impl AttachContext for S {}
/// impl DebugWithContext for S {
///     fn fmt(&self, _ctx: &Context, f: &mut fmt::Formatter<'_>) -> fmt::Result {
///         write!(f, "{}", self.i)
///     }
/// }
/// fn test() {
///     let ctx = Context::new();
///     dbg!(S {i: 64 }.with_ctx(&ctx));
///     let sv = vec![S { i: 0 }, S { i: 1 }, S { i: 2 }];
///     dbg!(sv.iter().with_ctx(&ctx));
/// }
/// // Calling `test` will print:
/// // [
/// //    0,
/// //    1,
/// //    2,
/// // ]
/// ```
pub trait DebugWithContext: AttachContext {
    fn fmt(&self, ctx: &Context, f: &mut fmt::Formatter<'_>) -> fmt::Result;
}

impl<T: DebugWithContext> fmt::Debug for WithContext<'_, '_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.t.fmt(self.ctx, f)
    }
}

// Implement [DebugWithContext] for any clonable [Iterator] whose [Item](Iterator::Item)
// implements [DebugWithContext].
// We need to clone the iterator because `fmt` below doesn't allow consuming it.
impl<'c, 't, T: 't + DebugWithContext, I: Iterator<Item = &'t T> + Clone> fmt::Debug
    for IterWithContext<'c, I>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// Check and ensure correctness.
pub trait Verify {
    fn verify(&self, ctx: &Context) -> Result<(), CompilerError>;
}

/// Anything that has a name.
pub trait Named {
    fn get_name(&self, ctx: &Context) -> String;
}

pub type ParsableState<'a, Input> = combine::stream::state::Stream<Input, &'a mut Context>;

/// Any object that can be parsed from its [DisplayWithContext] text.
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
