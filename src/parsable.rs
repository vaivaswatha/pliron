//! IR objects that can be parsed from their text representation.

use std::collections::hash_map::Entry;

use crate::{
    basic_block::BasicBlock,
    context::{Context, Ptr},
    dialects::builtin::{
        op_interfaces::{IsolatedFromAboveInterface, OneResultInterface},
        ops::ForwardRefOp,
    },
    error::{self, Result},
    identifier::Identifier,
    input_err,
    location::{self, Located, Location},
    op::op_impls,
    operation::Operation,
    use_def_lists::Value,
};
use combine::{
    easy::{self, Errors, ParseError},
    error::{StdParseResult2, Tracked},
    stream::{
        self, buffered,
        position::{self, SourcePosition},
        state::Stream,
        IteratorStream,
    },
    Parser, Positioned, StreamOnce,
};
use rustc_hash::FxHashMap;
use thiserror::Error;

/// State during parsing of any [Parsable] object.
/// Every parser implemented using [Parsable] will be passed
/// a mutable reference (wrapped with [StateStream]) to this state.
pub struct State<'a> {
    pub ctx: &'a mut Context,
    pub(crate) name_tracker: NameTracker,
    pub src: location::Source,
}

impl<'a> State<'a> {
    /// Create a new empty [State].
    pub fn new(ctx: &'a mut Context, src: location::Source) -> State {
        State {
            ctx,
            name_tracker: NameTracker::default(),
            src,
        }
    }
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
pub type StateStream<'a> = Stream<
    buffered::Stream<
        easy::Stream<
            stream::position::Stream<stream::IteratorStream<CharIterator<'a>>, SourcePosition>,
        >,
    >,
    State<'a>,
>;

impl<'a> Located for StateStream<'a> {
    fn loc(&self) -> location::Location {
        location::Location::SrcPos {
            src: self.state.src,
            pos: self.position(),
        }
    }

    fn set_loc(&mut self, _loc: Location) {
        panic!("Cannot set location of parser");
    }
}

pub type ParseResult<'a, T> = StdParseResult2<T, <StateStream<'a> as StreamOnce>::Error>;

/// Any object that can be parsed from its [Printable](crate::printable::Printable) text.
///
/// Implement [parse](Parsable::parse) and call [parser](Parsable::parser)
/// to get a parser combinator that can be combined with any other parser
/// from the [combine] library.
///
/// The [parse](Parsable::parse) function may take arguments whose type is
/// specified and constrained by the associated type [Parsable::Arg].
/// Example:
/// ```
/// use combine::{
///     Parser, Stream, StreamOnce, easy, stream::position,
///     parser::char::digit, many1
/// };
/// use pliron::{context::Context, parsable::
///     { state_stream_from_iterator, StateStream, Parsable, State, ParseResult},
///     location::Source,
/// };
/// #[derive(PartialEq, Eq)]
/// struct Number { n: u64 }
/// impl Parsable for Number {
///     type Arg = ();
///     type Parsed = Number;
///     fn parse<'a>(
///         state_stream: &mut StateStream<'a>,
///         arg: Self::Arg,
///     ) -> ParseResult<'a, Self::Parsed> {
///         many1::<String, _, _>(digit())
///         .map(|digits| {
///             let _ : &mut Context = state_stream.state.ctx;
///             Number { n: digits.parse::<u64>().unwrap() }
///         })
///         .parse_stream(&mut state_stream.stream).into()
///     }
/// }
/// let mut ctx = Context::new();
/// let state_stream = state_stream_from_iterator("100".chars(), State::new(&mut ctx, Source::InMemory));
/// assert!(Number::parser(()).parse(state_stream).unwrap().0 == Number { n: 100 });
///
/// ```
pub trait Parsable {
    /// Type of the argument that must be passed to the parser.
    type Arg: Clone + 'static;
    /// The type of the parsed entity.
    type Parsed;

    /// Define a parser using existing combinators and call
    /// `into` on [Parser::parse_stream] to get the final [ParseResult].
    /// Use [state_stream.state](StateStream::state) as necessary.
    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed>;

    /// Get a parser combinator that can work on [StateStream] as its input.
    fn parser<'a>(
        arg: Self::Arg,
    ) -> Box<dyn Parser<StateStream<'a>, Output = Self::Parsed, PartialState = ()> + 'a> {
        combine::parser(move |parsable_state: &mut StateStream<'a>| {
            Self::parse(parsable_state, arg.clone())
        })
        .boxed()
    }

    /// Same as [Self::parser] but takes a unit reference for use as [ParserFn]
    fn parser_fn<'a>(
        _: &'a (),
        arg: Self::Arg,
    ) -> Box<dyn Parser<StateStream<'a>, Output = Self::Parsed, PartialState = ()> + 'a> {
        Self::parser(arg)
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
pub type ParserFn<Arg, Parsed> =
    for<'a> fn(
        _: &'a (),
        arg: Arg,
    ) -> Box<dyn Parser<StateStream<'a>, Output = Parsed, PartialState = ()> + 'a>;

/// Convert [Result] into [StdParseResult2].
/// Enables using `?` on [Result] during parsing.
pub trait IntoParseResult<'a, T> {
    fn into_parse_result(self) -> StdParseResult2<T, <StateStream<'a> as StreamOnce>::Error>;
}

impl<'a, T> IntoParseResult<'a, T> for Result<T> {
    fn into_parse_result(self) -> StdParseResult2<T, <StateStream<'a> as StreamOnce>::Error> {
        match self {
            Ok(t) => combine::ParseResult::CommitOk(t),
            Err(e) => combine::ParseResult::CommitErr(e.into()),
        }
        .into()
    }
}

impl<'a> From<error::Error> for ParseError<StateStream<'a>> {
    fn from(value: error::Error) -> Self {
        let position = if let Location::SrcPos { pos, .. } = value.loc {
            pos
        } else {
            SourcePosition::default()
        };
        easy::Errors::from_errors(position, vec![easy::Error::Other(value.err)])
    }
}

impl<'a> From<error::Error>
    for combine::error::Commit<Tracked<Errors<char, char, SourcePosition>>>
{
    fn from(value: error::Error) -> Self {
        let res: StdParseResult2<(), ParseError<StateStream<'a>>> =
            combine::ParseResult::CommitErr(value.into()).into();
        res.err().unwrap()
    }
}

/// Serves a similar purpose to what [ForwardRefOp] serves for SSA names.
enum LabelRef {
    ForwardRef(Ptr<BasicBlock>),
    Defined(Ptr<BasicBlock>),
}

impl LabelRef {
    fn get_label(&self) -> Ptr<BasicBlock> {
        match self {
            LabelRef::ForwardRef(label) => *label,
            LabelRef::Defined(label) => *label,
        }
    }
}

/// Utility for parsing SSA names and block labels.
#[derive(Default)]
pub(crate) struct NameTracker {
    ssa_name_scope: Vec<FxHashMap<Identifier, Value>>,
    block_label_scope: Vec<FxHashMap<Identifier, LabelRef>>,
}

#[derive(Error, Debug)]
#[error("Identifier {0} was not resolved to any definition in the scope")]
pub struct UnresolvedReference(Identifier);

#[derive(Error, Debug)]
#[error("Identifier {0} defined more than once in the scope")]
pub struct MultipleDefinitions(Identifier);

impl NameTracker {
    /// An SSA use is seen. Get its [definition value][Value]
    /// or return a [forward reference][ForwardRefOp] that will
    /// be updated when the actual definition is seen.
    pub(crate) fn ssa_use(&mut self, ctx: &mut Context, id: &Identifier) -> Value {
        let scope = self
            .ssa_name_scope
            .last_mut()
            .expect("NameTracker doesn't have an active scope.");
        match scope.entry(id.clone()) {
            Entry::Occupied(occ) => *occ.get(),
            Entry::Vacant(vac) => {
                // Insert a forward reference.
                let forward_def = ForwardRefOp::new(ctx).get_result(ctx);
                vac.insert(forward_def);
                forward_def
            }
        }
    }

    /// Register an SSA definition. If `id` is already associated with a
    /// [forward reference][ForwardRefOp], update and replace all uses with `def`.
    pub(crate) fn ssa_def(
        &mut self,
        ctx: &mut Context,
        id: &(Identifier, Location),
        def: Value,
    ) -> Result<()> {
        let scope = self
            .ssa_name_scope
            .last_mut()
            .expect("NameTracker doesn't have an active scope.");

        match scope.entry(id.0.clone()) {
            Entry::Occupied(mut occ) => match occ.get_mut() {
                Value::OpResult { op, res_idx: _ } => {
                    let fref_opt = Operation::get_op(*op, ctx)
                        .downcast_ref::<ForwardRefOp>()
                        .map(|op| op.get_result(ctx));
                    if let Some(fref) = fref_opt {
                        // If there's already a def and its a forward ref, replace that.
                        fref.replace_some_uses_with(ctx, |_, _| true, &def);
                        Operation::erase(*op, ctx);
                        occ.insert(def);
                    } else {
                        // There's another def and it isn't a forward ref.
                        input_err!(id.1.clone(), MultipleDefinitions(id.0.clone()))?
                    }
                }
                Value::BlockArgument { .. } => {
                    // There's another def and it isn't a forward ref.
                    input_err!(id.1.clone(), MultipleDefinitions(id.0.clone()))?
                }
            },
            Entry::Vacant(vac) => {
                vac.insert(def);
            }
        }
        Ok(())
    }

    /// A [BasicBlock] use is seen. Get the actual block it refers to.
    /// If the block wasn't seen yet, create one now. When exiting the scope,
    /// if the block ends up not being seen, an undefined reference error is returned.
    pub(crate) fn block_use(&mut self, ctx: &mut Context, id: &Identifier) -> Ptr<BasicBlock> {
        let scope = self
            .block_label_scope
            .last_mut()
            .expect("NameTracker doesn't have an active scope.");
        match scope.entry(id.clone()) {
            Entry::Occupied(occ) => occ.get().get_label(),
            Entry::Vacant(vac) => {
                // Insert a forward reference.
                let block_forward = BasicBlock::new(ctx, Some(id.clone()), vec![]);
                vac.insert(LabelRef::ForwardRef(block_forward));
                block_forward
            }
        }
    }

    /// A [BasicBlock] def is seen. If refs was seen earlier,
    /// they are all updated now to refer to the provided block instead.
    pub(crate) fn block_def(
        &mut self,
        ctx: &mut Context,
        id: &(Identifier, Location),
        block: Ptr<BasicBlock>,
    ) -> Result<()> {
        let scope = self
            .block_label_scope
            .last_mut()
            .expect("NameTracker doesn't have an active scope.");
        match scope.entry(id.0.clone()) {
            Entry::Occupied(mut occ) => match occ.get_mut() {
                LabelRef::ForwardRef(fref) => {
                    fref.retarget_some_preds_to(ctx, |_, _| true, block);
                    BasicBlock::erase(*fref, ctx);
                    occ.insert(LabelRef::Defined(block));
                }
                LabelRef::Defined(_) => {
                    input_err!(id.1.clone(), MultipleDefinitions(id.0.clone()))?
                }
            },
            Entry::Vacant(vac) => {
                vac.insert(LabelRef::Defined(block));
            }
        }
        Ok(())
    }

    /// Enter a new region.
    /// - If the parent op is [IsolatedFromAboveInterface],
    ///   then a new independent SSA name scope is created.
    /// - A new independent block label scope is always created.
    pub(crate) fn enter_region(&mut self, ctx: &Context, parent_op: Ptr<Operation>) {
        if op_impls::<dyn IsolatedFromAboveInterface>(&*Operation::get_op(parent_op, ctx)) {
            self.ssa_name_scope.push(FxHashMap::default());
        }
        self.block_label_scope.push(FxHashMap::default());
    }

    /// Exit a region.
    /// - If the parent op is [IsolatedFromAboveInterface], then the top SSA name scope is popped.
    /// - The top block label scope is popped.
    pub(crate) fn exit_region(
        &mut self,
        ctx: &Context,
        parent_op: Ptr<Operation>,
        loc: Location,
    ) -> Result<()> {
        if op_impls::<dyn IsolatedFromAboveInterface>(&*Operation::get_op(parent_op, ctx)) {
            // Check if there are any [ForwardRefOp].
            let ssa_scope = self
                .ssa_name_scope
                .pop()
                .expect("Exiting an isolated-from-above region which wasn't entered into.");
            for (id, op) in ssa_scope {
                if matches!(op, Value::OpResult { op, .. } if Operation::get_op(op, ctx).is::<ForwardRefOp>())
                {
                    input_err!(loc.clone(), UnresolvedReference(id.clone()))?
                }
            }
        }

        let label_scope = self
            .block_label_scope
            .pop()
            .expect("Exiting an isolated-from-above region which wasn't entered into.");

        // Check if there are any unresolved forward label references.
        for (id, op) in label_scope {
            if matches!(op, LabelRef::ForwardRef(_)) {
                input_err!(loc.clone(), UnresolvedReference(id.clone()))?
            }
        }

        Ok(())
    }
}
