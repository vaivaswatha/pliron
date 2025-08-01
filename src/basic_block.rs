//! A [BasicBlock] is a list of [Operation]s.

use combine::{
    parser::{Parser, char::spaces},
    sep_by, token,
};

use crate::{
    attribute::AttributeDict,
    builtin::op_interfaces::IsTerminatorInterface,
    common_traits::{Named, Verify},
    context::{ArenaCell, Context, Ptr, private::ArenaObj},
    debug_info::{get_block_arg_name, set_block_arg_name},
    identifier::Identifier,
    indented_block,
    irfmt::{
        parsers::{delimited_list_parser, location, spaced, type_parser},
        printers::{iter_with_sep, list_with_sep},
    },
    linked_list::{ContainsLinkedList, LinkedList, private},
    location::{Located, Location},
    op::op_impls,
    operation::{Operation, OperationParserConfig},
    parsable::{self, IntoParseResult, Parsable, ParseResult},
    printable::{self, ListSeparator, Printable, indented_nl},
    region::Region,
    result::Result,
    r#type::{TypeObj, Typed},
    utils::vec_exns::VecExtns,
    value::{DefNode, Value},
};

/// Argument to a [BasicBlock]
pub(crate) struct BlockArgument {
    /// The def containing the list of this argument's uses.
    pub(crate) def: DefNode<Value>,
    /// A [Ptr] to the [BasicBlock] of which this is an argument.
    pub(crate) def_block: Ptr<BasicBlock>,
    /// Index of this argument in the block's list of arguments.
    pub(crate) arg_idx: usize,
    /// The [Type](crate::type::Type) of this argument.
    pub(crate) ty: Ptr<TypeObj>,
}

impl Typed for BlockArgument {
    fn get_type(&self, _ctx: &Context) -> Ptr<TypeObj> {
        self.ty
    }
}

impl Named for BlockArgument {
    fn given_name(&self, ctx: &Context) -> Option<Identifier> {
        get_block_arg_name(ctx, self.def_block, self.arg_idx)
    }
    fn id(&self, ctx: &Context) -> Identifier {
        format!("{}_arg{}", self.def_block.deref(ctx).id(ctx), self.arg_idx)
            .try_into()
            .unwrap()
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
        write!(f, "{}: {}", self.unique_name(ctx), self.ty.disp(ctx))
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

/// A basic block contains a list of [Operation]s. It may have [arguments](Value::BlockArgument).
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
    pub attributes: AttributeDict,
    loc: Location,
}

impl Named for BasicBlock {
    fn given_name(&self, _ctx: &Context) -> Option<Identifier> {
        self.label.clone()
    }
    fn id(&self, _ctx: &Context) -> Identifier {
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
            attributes: AttributeDict::default(),
            loc: Location::Unknown,
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

    /// Get parent region.
    pub fn get_parent_region(&self) -> Option<Ptr<Region>> {
        self.region_links.parent_region
    }

    /// Get parent operation.
    pub fn get_parent_op(&self, ctx: &Context) -> Option<Ptr<Operation>> {
        self.get_parent_region()
            .map(|region| region.deref(ctx).get_parent_op())
    }

    /// Get idx'th argument as a Value.
    pub fn get_argument(&self, arg_idx: usize) -> Value {
        self.args
            .get(arg_idx)
            .map(|arg| arg.into())
            .unwrap_or_else(|| panic!("Block argument index {arg_idx} out of bounds"))
    }

    /// Get an iterator over the arguments
    pub fn arguments(&self) -> impl Iterator<Item = Value> + '_ {
        self.args.iter().map(Into::into)
    }

    /// Add a new argument with specified type. Returns idx at which it was added.
    pub fn add_argument(&mut self, ty: Ptr<TypeObj>) -> usize {
        self.args.push_back_with(|arg_idx| BlockArgument {
            def: DefNode::new(),
            def_block: self.self_ptr,
            arg_idx,
            ty,
        })
    }

    /// Get a reference to the idx'th argument.
    pub(crate) fn get_argument_ref(&self, arg_idx: usize) -> &BlockArgument {
        self.args
            .get(arg_idx)
            .unwrap_or_else(|| panic!("Block argument index {arg_idx} out of bounds"))
    }

    /// Get a mutable reference to the idx'th argument.
    pub(crate) fn get_argument_mut(&mut self, arg_idx: usize) -> &mut BlockArgument {
        self.args
            .get_mut(arg_idx)
            .unwrap_or_else(|| panic!("Block argument index {arg_idx} out of bounds"))
    }

    /// Get the number of arguments.
    pub fn get_num_arguments(&self) -> usize {
        self.args.len()
    }

    /// Get all successors of this block.
    pub fn succs(&self, ctx: &Context) -> Vec<Ptr<BasicBlock>> {
        self.get_tail()
            .expect("A well formed BasicBlock must have a terminator")
            .deref(ctx)
            .successors()
            .collect()
    }

    /// Get the block terminator, if one exists.
    pub fn get_terminator(&self, ctx: &Context) -> Option<Ptr<Operation>> {
        let last_opr = self.get_tail()?;
        let last_op = Operation::get_op(last_opr, ctx);
        op_impls::<dyn IsTerminatorInterface>(&*last_op).then_some(last_opr)
    }

    /// Insert an instruction at the end of this block, but before the terminator if it exists.
    pub fn insert_op_before_terminator(block: Ptr<Self>, op: Ptr<Operation>, ctx: &Context) {
        if let Some(term) = block.deref(ctx).get_terminator(ctx) {
            op.insert_before(ctx, term);
        } else {
            op.insert_at_back(block, ctx);
        }
    }

    /// Drop all uses that this block holds.
    pub fn drop_all_uses(ptr: Ptr<Self>, ctx: &Context) {
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
            !ptr.has_pred(ctx),
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

impl Located for BasicBlock {
    fn loc(&self) -> Location {
        self.loc.clone()
    }

    fn set_loc(&mut self, loc: Location) {
        self.loc = loc;
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
            list_with_sep(&self.args, ListSeparator::CharSpace(',')).print(ctx, state),
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
    ///  label(arg_1: type_1, ..., arg_n: type_n):
    ///    op_1;
    ///    ... ;
    ///    op_n
    fn parse<'a>(
        state_stream: &mut parsable::StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        let loc = state_stream.loc();

        let arg = (
            (location(), Identifier::parser(())).skip(spaced(token(':'))),
            type_parser().skip(spaces()),
        );
        let args = spaced(delimited_list_parser('(', ')', ',', arg)).skip(token(':'));
        let ops = spaces().with(sep_by::<Vec<_>, _, _, _>(
            Operation::parser(OperationParserConfig {
                look_for_outlined_attrs: false,
            })
            .skip(spaces()),
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
        for (arg_idx, (loc, name)) in arg_names.into_iter().enumerate() {
            let def: Value = (&block.deref(state_stream.state.ctx).args[arg_idx]).into();
            state_stream.state.name_tracker.ssa_def(
                state_stream.state.ctx,
                &(name.clone(), loc),
                def,
            )?;
            set_block_arg_name(state_stream.state.ctx, block, arg_idx, name);
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
