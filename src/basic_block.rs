//! A [BasicBlock] is a list of [Operation]s.

use combine::{
    between,
    parser::{char::spaces, Parser},
    position, sep_by, token,
};
use rustc_hash::FxHashMap;

use crate::{
    attribute::AttrObj,
    common_traits::{Named, Verify},
    context::{private::ArenaObj, ArenaCell, Context, Ptr},
    debug_info::{get_block_arg_name, set_block_arg_name},
    error::Result,
    identifier::Identifier,
    indented_block,
    irfmt::printers::{iter_with_sep, list_with_sep},
    linked_list::{private, ContainsLinkedList, LinkedList},
    location::{Located, Location},
    operation::Operation,
    parsable::{self, spaced, IntoParseResult, Parsable, ParseResult},
    printable::{self, indented_nl, ListSeparator, Printable},
    r#type::{type_parser, TypeObj, Typed},
    region::Region,
    use_def_lists::{DefNode, Value},
};

/// Argument to a [BasicBlock]
pub struct BlockArgument {
    /// The def containing the list of this argument's uses.
    pub(crate) def: DefNode<Value>,
    /// A [Ptr] to the [BasicBlock] of which this is an argument.
    def_block: Ptr<BasicBlock>,
    /// Index of this argument in the block's list of arguments.
    arg_idx: usize,
    /// The [Type](crate::type::Type) of this argument.
    ty: Ptr<TypeObj>,
}

impl BlockArgument {
    /// A [Ptr] to the [BasicBlock] of which this is an argument.
    pub fn get_def_block(&self) -> Ptr<BasicBlock> {
        self.def_block
    }

    /// Index of this argument in the block's list of arguments.
    pub fn get_arg_idx(&self) -> usize {
        self.arg_idx
    }

    /// Get the [Type](crate::type::Type) of this block argument.
    pub fn get_type(&self) -> Ptr<TypeObj> {
        self.ty
    }
}

impl Typed for BlockArgument {
    fn get_type(&self, _cfg: &Context) -> Ptr<TypeObj> {
        self.ty
    }
}

impl Named for BlockArgument {
    fn given_name(&self, ctx: &Context) -> Option<String> {
        get_block_arg_name(ctx, self.get_def_block(), self.arg_idx)
    }
    fn id(&self, ctx: &Context) -> String {
        format!("{}_arg{}", self.def_block.deref(ctx).id(ctx), self.arg_idx)
    }
}

impl From<&BlockArgument> for Value {
    fn from(value: &BlockArgument) -> Self {
        Value::BlockArgument {
            block: value.def_block,
            arg_idx: value.arg_idx,
        }
    }
}

impl Printable for BlockArgument {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        write!(f, "{}:{}", self.unique_name(ctx), self.get_type().disp(ctx))
    }
}

/// [Operation]s contained in this [BasicBlock]
#[derive(Default)]
pub struct OpsInBlock {
    first: Option<Ptr<Operation>>,
    last: Option<Ptr<Operation>>,
}

/// Links a [BasicBlock] with other blocks and the container [Region].
#[derive(Default)]
struct RegionLinks {
    /// Parent region of this block.
    parent_region: Option<Ptr<Region>>,
    /// The next block in the region's list of block.
    next_block: Option<Ptr<BasicBlock>>,
    /// The previous block in the region's list of blocks.
    prev_block: Option<Ptr<BasicBlock>>,
}

/// A basic block contains a list of [Operation]s. It may have [arguments](BlockArgument).
pub struct BasicBlock {
    pub(crate) self_ptr: Ptr<BasicBlock>,
    pub(crate) label: Option<Identifier>,
    pub(crate) ops_list: OpsInBlock,
    pub(crate) args: Vec<BlockArgument>,
    pub(crate) preds: DefNode<Ptr<BasicBlock>>,
    /// Links to the parent [Region] and
    /// previous and next [BasicBlock]s in the block.
    region_links: RegionLinks,
    /// A dictionary of attributes.
    pub attributes: FxHashMap<&'static str, AttrObj>,
}

impl Named for BasicBlock {
    fn given_name(&self, _ctx: &Context) -> Option<String> {
        self.label.as_ref().map(|id| id.clone().into())
    }
    fn id(&self, _ctx: &Context) -> String {
        self.self_ptr.make_name("block")
    }
}

impl BasicBlock {
    /// Create a new Basic Block.
    pub fn new(
        ctx: &mut Context,
        label: Option<Identifier>,
        arg_types: Vec<Ptr<TypeObj>>,
    ) -> Ptr<BasicBlock> {
        let f = |self_ptr: Ptr<BasicBlock>| BasicBlock {
            self_ptr,
            label,
            args: vec![],
            ops_list: OpsInBlock::default(),
            preds: DefNode::new(),
            region_links: RegionLinks::default(),
            attributes: FxHashMap::default(),
        };
        let newblock = Self::alloc(ctx, f);
        // Let's update the args of the new block. Easier to do it here than during creation.
        let args = arg_types
            .into_iter()
            .enumerate()
            .map(|(arg_idx, ty)| BlockArgument {
                def: DefNode::new(),
                def_block: newblock,
                arg_idx,
                ty,
            })
            .collect();
        newblock.deref_mut(ctx).args = args;
        // We're done.
        newblock
    }

    /// Get idx'th argument as a Value.
    pub fn get_argument(&self, arg_idx: usize) -> Option<Value> {
        self.args.get(arg_idx).map(|arg| arg.into())
    }

    /// Get a reference to the idx'th argument.
    pub(crate) fn get_argument_ref(&self, arg_idx: usize) -> Option<&BlockArgument> {
        self.args.get(arg_idx)
    }

    /// Get a mutable reference to the idx'th argument.
    pub(crate) fn get_argument_mut(&mut self, arg_idx: usize) -> Option<&mut BlockArgument> {
        self.args.get_mut(arg_idx)
    }

    /// Get the number of arguments.
    pub fn get_num_arguments(&self) -> usize {
        self.args.len()
    }

    /// Does this block a predecessor?
    pub fn has_pred(&self) -> bool {
        self.preds.has_use()
    }

    /// Number of predecessors to this block.
    pub fn num_preds(&self) -> usize {
        self.preds.num_uses()
    }

    /// Drop all uses that this block holds.
    pub fn drop_all_uses(ptr: Ptr<Self>, ctx: &mut Context) {
        let ops: Vec<_> = ptr.deref(ctx).iter(ctx).collect();
        for op in ops {
            Operation::drop_all_uses(op, ctx);
        }
    }

    /// Unlink and deallocate this block and everything that it contains.
    /// There must not be any uses outside the block.
    pub fn erase(ptr: Ptr<Self>, ctx: &mut Context) {
        Self::drop_all_uses(ptr, ctx);
        assert!(
            !ptr.deref(ctx).has_pred(),
            "BasicBlock with predecessor(s) being erased"
        );

        if ptr.deref(ctx).iter(ctx).any(|op| op.deref(ctx).has_use()) {
            panic!("Attemping to erase block which has a use outside the block")
        }
        if ptr.is_linked(ctx) {
            ptr.unlink(ctx);
        }
        ArenaObj::dealloc(ptr, ctx);
    }
}

impl private::ContainsLinkedList<Operation> for BasicBlock {
    fn set_head(&mut self, head: Option<Ptr<Operation>>) {
        self.ops_list.first = head;
    }

    fn set_tail(&mut self, tail: Option<Ptr<Operation>>) {
        self.ops_list.last = tail;
    }
}

impl ContainsLinkedList<Operation> for BasicBlock {
    fn get_head(&self) -> Option<Ptr<Operation>> {
        self.ops_list.first
    }

    fn get_tail(&self) -> Option<Ptr<Operation>> {
        self.ops_list.last
    }
}

impl PartialEq for BasicBlock {
    fn eq(&self, other: &Self) -> bool {
        self.self_ptr == other.self_ptr
    }
}

impl private::LinkedList for BasicBlock {
    type ContainerType = Region;
    fn set_next(&mut self, next: Option<Ptr<Self>>) {
        self.region_links.next_block = next;
    }
    fn set_prev(&mut self, prev: Option<Ptr<Self>>) {
        self.region_links.prev_block = prev;
    }
    fn set_container(&mut self, container: Option<Ptr<Self::ContainerType>>) {
        self.region_links.parent_region = container;
    }
}

impl LinkedList for BasicBlock {
    fn get_next(&self) -> Option<Ptr<Self>> {
        self.region_links.next_block
    }
    fn get_prev(&self) -> Option<Ptr<Self>> {
        self.region_links.prev_block
    }
    fn get_container(&self) -> Option<Ptr<Self::ContainerType>> {
        self.region_links.parent_region
    }
}

impl ArenaObj for BasicBlock {
    fn get_arena(ctx: &Context) -> &ArenaCell<Self> {
        &ctx.basic_blocks
    }
    fn get_arena_mut(ctx: &mut Context) -> &mut ArenaCell<Self> {
        &mut ctx.basic_blocks
    }
    fn dealloc_sub_objects(ptr: Ptr<Self>, ctx: &mut Context) {
        let ops: Vec<_> = ptr.deref_mut(ctx).iter(ctx).collect();
        for op in ops {
            ArenaObj::dealloc(op, ctx);
        }
    }
    fn get_self_ptr(&self, _ctx: &Context) -> Ptr<Self> {
        self.self_ptr
    }
}

impl Verify for BasicBlock {
    fn verify(&self, ctx: &Context) -> Result<()> {
        self.iter(ctx).try_for_each(|op| op.deref(ctx).verify(ctx))
    }
}

impl Printable for BasicBlock {
    fn fmt(
        &self,
        ctx: &Context,
        state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        write!(
            f,
            "^{}({}):",
            self.unique_name(ctx),
            list_with_sep(&self.args, ListSeparator::Char(',')).print(ctx, state),
        )?;

        indented_block!(state, {
            write!(
                f,
                "{}{}",
                indented_nl(state),
                iter_with_sep(self.iter(ctx), ListSeparator::CharNewline(';')).print(ctx, state),
            )?;
        });

        Ok(())
    }
}

impl Parsable for BasicBlock {
    type Arg = ();
    type Parsed = Ptr<BasicBlock>;

    ///  A basic block is
    ///  label(arg_1:type_1, ..., arg_n:type_n):
    ///    op_1;
    ///    ... ;
    ///    op_n
    fn parse<'a>(
        state_stream: &mut parsable::StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        let loc = state_stream.loc();
        let src = loc
            .source()
            .expect("Location from Parsable must be Location::SrcPos");

        let arg = (
            (position(), Identifier::parser(())).skip(spaced(token(':'))),
            type_parser().skip(spaces()),
        );
        let args = spaced(between(
            token('('),
            token(')'),
            spaces().with(sep_by::<Vec<_>, _, _, _>(arg, token(',').skip(spaces()))),
        ))
        .skip(token(':'));
        let ops = spaces().with(sep_by::<Vec<_>, _, _, _>(
            Operation::parser(()).skip(spaces()),
            token(';').skip(spaces()),
        ));

        let label = spaced(token('^').with(Identifier::parser(())));
        let (label, args, ops) = (label, args, ops)
            .parse_stream(state_stream)
            .into_result()?
            .0;

        // We've parsed the components. Now construct the result.
        let (arg_names, arg_types): (Vec<_>, Vec<_>) = args.into_iter().unzip();
        let block = BasicBlock::new(state_stream.state.ctx, Some(label.clone()), arg_types);
        for (arg_idx, (pos, name)) in arg_names.into_iter().enumerate() {
            let def: Value = (&block.deref(state_stream.state.ctx).args[arg_idx]).into();
            let name_string = name.to_string();
            state_stream.state.name_tracker.ssa_def(
                state_stream.state.ctx,
                &(name, Location::SrcPos { src, pos }),
                def,
            )?;
            set_block_arg_name(state_stream.state.ctx, block, arg_idx, name_string);
        }
        for op in ops {
            op.insert_at_back(block, state_stream.state.ctx);
        }
        state_stream
            .state
            .name_tracker
            .block_def(state_stream.state.ctx, &(label, loc), block)?;
        Ok(block).into_parse_result()
    }
}
