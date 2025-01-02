//! Regions are containers for [BasicBlock]s within an [Operation].
use combine::{parser::char::spaces, token, Parser};

use crate::{
    basic_block::BasicBlock,
    common_traits::Verify,
    context::{private::ArenaObj, Context, Ptr},
    indented_block,
    linked_list::{private, ContainsLinkedList},
    location::Located,
    operation::Operation,
    parsable::{self, IntoParseResult, Parsable, ParseResult},
    printable::{self, fmt_indented_newline, fmt_iter, ListSeparator, Printable},
    result::Result,
};

/// [BasicBlock]s contained in this [Region].
#[derive(Default)]
struct BlocksInRegion {
    first: Option<Ptr<BasicBlock>>,
    last: Option<Ptr<BasicBlock>>,
}

/// A region is an ordered list of basic blocks contained in an Operation.
/// The first block, called the entry block is special. Its arguments
/// are considered to be the arguments to the region. It cannot have any
/// CFG predecessors (i.e., no block can branch to the entry block).
/// See [MLIR Region description](https://mlir.llvm.org/docs/LangRef/#regions).
pub struct Region {
    pub(crate) self_ptr: Ptr<Region>,
    pub(crate) parent_op: Ptr<Operation>,
    blocks: BlocksInRegion,
}

impl Region {
    /// Create a new Region.
    pub(crate) fn new(ctx: &mut Context, parent_op: Ptr<Operation>) -> Ptr<Region> {
        let f = |self_ptr: Ptr<Region>| Region {
            self_ptr,
            blocks: BlocksInRegion::default(),
            parent_op,
        };
        Self::alloc(ctx, f)
    }

    /// Move this [Region] to (the end of) a different [Operation].
    /// If `new_parent_op` is same as the current parent, no action.
    /// Indices of other regions in the current parent will be invalidated.
    pub fn move_to_op(ptr: Ptr<Self>, new_parent_op: Ptr<Operation>, ctx: &mut Context) {
        let src = ptr.deref(ctx).get_parent_op();
        if src == new_parent_op {
            return;
        }
        let regions = &mut src.deref_mut(ctx).regions;
        regions.swap_remove(
            regions
                .iter()
                .position(|x| *x == ptr)
                .expect("Region missing in it's current parent Operations"),
        );
        new_parent_op.deref_mut(ctx).regions.push(ptr);
        ptr.deref_mut(ctx).parent_op = new_parent_op;
    }

    /// Get the operation that contains this region.
    pub fn get_parent_op(&self) -> Ptr<Operation> {
        self.parent_op
    }

    /// Drop all uses that this region holds.
    pub fn drop_all_uses(ptr: Ptr<Self>, ctx: &Context) {
        let blocks: Vec<_> = ptr.deref(ctx).iter(ctx).collect();
        for block in blocks {
            BasicBlock::drop_all_uses(block, ctx);
        }
    }
}

impl private::ContainsLinkedList<BasicBlock> for Region {
    fn set_head(&mut self, head: Option<Ptr<BasicBlock>>) {
        self.blocks.first = head;
    }
    fn set_tail(&mut self, tail: Option<Ptr<BasicBlock>>) {
        self.blocks.last = tail;
    }
}

impl ContainsLinkedList<BasicBlock> for Region {
    fn get_head(&self) -> Option<Ptr<BasicBlock>> {
        self.blocks.first
    }
    fn get_tail(&self) -> Option<Ptr<BasicBlock>> {
        self.blocks.last
    }
}

impl ArenaObj for Region {
    fn get_arena(ctx: &Context) -> &crate::context::ArenaCell<Self> {
        &ctx.regions
    }

    fn get_arena_mut(ctx: &mut Context) -> &mut crate::context::ArenaCell<Self> {
        &mut ctx.regions
    }

    fn get_self_ptr(&self, _ctx: &Context) -> Ptr<Self> {
        self.self_ptr
    }

    fn dealloc_sub_objects(ptr: Ptr<Self>, ctx: &mut Context) {
        let blocks: Vec<_> = ptr.deref_mut(ctx).iter(ctx).collect();
        for block in blocks {
            ArenaObj::dealloc(block, ctx);
        }
    }
}

impl Verify for Region {
    fn verify(&self, ctx: &Context) -> Result<()> {
        self.iter(ctx).try_for_each(|op| op.deref(ctx).verify(ctx))
    }
}

impl Printable for Region {
    fn fmt(
        &self,
        ctx: &Context,
        state: &printable::State,
        f: &mut core::fmt::Formatter<'_>,
    ) -> core::fmt::Result {
        fmt_indented_newline(state, f)?;
        write!(f, "{{")?;

        indented_block!(state, {
            fmt_indented_newline(state, f)?;
            fmt_iter(self.iter(ctx), ctx, state, ListSeparator::Newline, f)?;
        });

        fmt_indented_newline(state, f)?;
        write!(f, "}}")?;
        Ok(())
    }
}

/// Parse a [Region].
impl Parsable for Region {
    type Arg = Ptr<Operation>;
    type Parsed = Ptr<Region>;

    /// A region is a sequence of [BasicBlock]s between '{' and '}'.
    /// Creating a region requires a [Ptr] to the parent [Operation].
    fn parse<'a>(
        state_stream: &mut parsable::StateStream<'a>,
        parent_op: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        let loc = state_stream.loc();
        state_stream
            .state
            .name_tracker
            .enter_region(state_stream.state.ctx, parent_op);

        let block_list_parser = spaces().with(combine::many::<Vec<_>, _, _>(
            BasicBlock::parser(()).skip(spaces()),
        ));
        let braces_bounded_region_parser =
            combine::between(token('{'), token('}'), block_list_parser);

        let mut region_parser = braces_bounded_region_parser.then(|blocks| {
            combine::parser(move |state_stream: &mut parsable::StateStream| {
                let region = Operation::add_region(parent_op, state_stream.state.ctx);
                for block in blocks.iter() {
                    block.insert_at_back(region, state_stream.state.ctx);
                }
                Ok(region).into_parse_result()
            })
        });

        let result = region_parser.parse_stream(state_stream);

        state_stream
            .state
            .name_tracker
            .exit_region(state_stream.state.ctx, parent_op, loc)?;

        result.into()
    }
}
