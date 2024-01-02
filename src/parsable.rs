//! IR objects that can be parsed from their text representation.

use std::collections::hash_map::Entry;

use crate::{
    basic_block::BasicBlock,
    context::{Context, Ptr},
    dialects::builtin::{
        op_interfaces::{IsolatedFromAboveInterface, OneResultInterface},
        ops::ForwardRefOp,
    },
    error::Result,
    identifier::Identifier,
    input_err,
    location::{self, Located},
    op::op_impls,
    operation::Operation,
    use_def_lists::Value,
};
use combine::{
    easy,
    error::StdParseResult2,
    parser::char::spaces,
    stream::{
        self, buffered,
        position::{self, SourcePosition},
        IteratorStream,
    },
    ParseResult, Parser, Positioned, Stream, StreamOnce,
};
use rustc_hash::FxHashMap;
use thiserror::Error;

/// State during parsing of any [Parsable] object.
/// Every parser implemented using [Parsable] will be passed
/// a mutable reference (wrapped with [StateStream]) to this state.
pub struct State<'a> {
    pub ctx: &'a mut Context,
    pub name_tracker: NameTracker,
    pub src: location::Source,
}

impl<'a> State<'a> {
    /// Create a new [State] with an empty [NameTracker].
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
pub type StateStream<'a> = stream::state::Stream<
    buffered::Stream<
        easy::Stream<
            stream::position::Stream<stream::IteratorStream<CharIterator<'a>>, SourcePosition>,
        >,
    >,
    State<'a>,
>;

impl<'a> Located for StateStream<'a> {
    fn location(&self) -> location::Location {
        location::Location::SrcPos {
            src: self.state.src,
            pos: self.position(),
        }
    }
}

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
///     parser::char::digit, many1, error::StdParseResult2
/// };
/// use pliron::{context::Context, parsable::
///     { state_stream_from_iterator, StateStream, Parsable, State},
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
///     ) -> StdParseResult2<Self::Parsed, <StateStream<'a> as StreamOnce>::Error> {
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
    /// `into` on [Parser::parse_stream] to get the final [StdParseResult2].
    /// Use [state_stream.state](StateStream::state) as necessary.
    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        arg: Self::Arg,
    ) -> StdParseResult2<Self::Parsed, <StateStream<'a> as StreamOnce>::Error>;

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

/// Convert [Result] into [StdParseResult2].
/// Enables using `?` on [Result] during parsing.
pub trait IntoStdParseResult2<'a, T> {
    fn into_pres2(
        self,
        pos: SourcePosition,
    ) -> StdParseResult2<T, <StateStream<'a> as StreamOnce>::Error>;
}

impl<'a, T> IntoStdParseResult2<'a, T> for Result<T> {
    fn into_pres2(
        self,
        pos: SourcePosition,
    ) -> StdParseResult2<T, <StateStream<'a> as StreamOnce>::Error> {
        match self {
            Ok(t) => ParseResult::CommitOk(t).into(),
            Err(e) => ParseResult::CommitErr(easy::Errors::from_errors(
                pos,
                vec![easy::Error::Message(e.err.to_string().into())],
            ))
            .into(),
        }
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
pub struct NameTracker {
    ssa_name_scope: Vec<FxHashMap<Identifier, Value>>,
    block_label_scope: Vec<FxHashMap<Identifier, LabelRef>>,
}

#[derive(Error, Debug)]
#[error("Identifier {0} was not resolved to any definition")]
pub struct UnresolvedReference(Identifier);

#[derive(Error, Debug)]
#[error("Identifier {0} defined more than once in the scope")]
pub struct MultipleDefinitions(Identifier);

impl NameTracker {
    /// An SSA use is seen. Get its [definition value][Value]
    /// or return a [forward reference][ForwardRefOp] that will
    /// be updated when the actual definition is seen.
    pub fn ssa_use(&mut self, ctx: &mut Context, id: &Identifier) -> Value {
        let scope = self
            .ssa_name_scope
            .last_mut()
            .expect("NameTracker doesn't have an active scope.");
        match scope.entry(id.clone()) {
            Entry::Occupied(occ) => *occ.get(),
            Entry::Vacant(vac) => {
                // Insert a forward reference.
                let forward_def = ForwardRefOp::new_unlinked(ctx).get_result(ctx);
                vac.insert(forward_def);
                forward_def
            }
        }
    }

    /// Register an SSA definition. If `id` is already associated with a
    /// [forward reference][ForwardRefOp], update and replace all uses with `def`.
    pub fn ssa_def(&mut self, ctx: &mut Context, id: &Identifier, def: Value) -> Result<()> {
        let scope = self
            .ssa_name_scope
            .last_mut()
            .expect("NameTracker doesn't have an active scope.");

        match scope.entry(id.clone()) {
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
                        return input_err!(MultipleDefinitions(id.clone()));
                    }
                }
                Value::BlockArgument { .. } => {
                    // There's another def and it isn't a forward ref.
                    return input_err!(MultipleDefinitions(id.clone()));
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
    pub fn block_use(&mut self, ctx: &mut Context, id: &Identifier) -> Ptr<BasicBlock> {
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
    pub fn block_def(
        &mut self,
        ctx: &mut Context,
        id: &Identifier,
        block: Ptr<BasicBlock>,
    ) -> Result<()> {
        let scope = self
            .block_label_scope
            .last_mut()
            .expect("NameTracker doesn't have an active scope.");
        match scope.entry(id.clone()) {
            Entry::Occupied(mut occ) => match occ.get_mut() {
                LabelRef::ForwardRef(fref) => {
                    fref.retarget_some_preds_to(ctx, |_, _| true, block);
                    BasicBlock::erase(*fref, ctx);
                    occ.insert(LabelRef::Defined(block));
                }
                LabelRef::Defined(_) => {
                    return input_err!(MultipleDefinitions(id.clone()));
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
    pub fn enter_region(&mut self, ctx: &Context, parent_op: Ptr<Operation>) {
        if op_impls::<dyn IsolatedFromAboveInterface>(&*Operation::get_op(parent_op, ctx)) {
            self.ssa_name_scope.push(FxHashMap::default());
        }
        self.block_label_scope.push(FxHashMap::default());
    }

    /// Exit a region.
    /// - If the parent op is [IsolatedFromAboveInterface], then the top SSA name scope is popped.
    /// - The top block label scope is popped.
    pub fn exit_region(&mut self, ctx: &Context, parent_op: Ptr<Operation>) -> Result<()> {
        if op_impls::<dyn IsolatedFromAboveInterface>(&*Operation::get_op(parent_op, ctx)) {
            // Check if there are any [ForwardRefOp].
            let ssa_scope = self
                .ssa_name_scope
                .pop()
                .expect("Exiting an isolated-from-above region which wasn't entered into.");
            for (id, op) in ssa_scope {
                if matches!(op, Value::OpResult { op, .. } if Operation::get_op(op, ctx).is::<ForwardRefOp>())
                {
                    return input_err!(UnresolvedReference(id.clone()));
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
                return input_err!(UnresolvedReference(id.clone()));
            }
        }

        Ok(())
    }
}
