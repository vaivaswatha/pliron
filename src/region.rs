//! Regions are containers for [BasicBlock]s within an [Operation].
use combine::{Parser, parser::char::spaces, token};
use rustc_hash::FxHashMap;

use crate::{
    basic_block::BasicBlock, common_traits::Verify, context::{Context, Ptr, private::ArenaObj}, graph, indented_block, linked_list::{ContainsLinkedList, private}, location::Located, operation::Operation, parsable::{self, IntoParseResult, Parsable, ParseResult}, printable::{self, ListSeparator, Printable, fmt_indented_newline, fmt_iter}, result::Result
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
    pub fn move_to_op(ptr: Ptr<Self>, new_parent_op: Ptr<Operation>, ctx: &Context) {
        let src = ptr.deref(ctx).get_parent_op();
        if src == new_parent_op {
            return;
        }
        let regions = &mut src.deref_mut(ctx).regions;
        regions.swap_remove(
            regions
                .iter()
                .position(|x| *x == ptr)
                .expect("Region missing in it's current parent Operation"),
        );
        new_parent_op.deref_mut(ctx).regions.push(ptr);
        ptr.deref_mut(ctx).parent_op = new_parent_op;
    }

    /// Get the operation that contains this region.
    pub fn get_parent_op(&self) -> Ptr<Operation> {
        self.parent_op
    }

    /// Get the index of this region in its parent operation.
    pub fn get_index_in_parent(&self, ctx: &Context) -> usize {
        let parent_op = self.get_parent_op();
        parent_op
            .deref(ctx)
            .regions
            .iter()
            .position(|r| *r == self.self_ptr)
            .expect("Region missing in it's parent Operation")
    }

    /// Drop all uses that this region holds.
    pub fn drop_all_uses(ptr: Ptr<Self>, ctx: &Context) {
        let blocks: Vec<_> = ptr.deref(ctx).iter(ctx).collect();
        for block in blocks {
            BasicBlock::drop_all_uses(block, ctx);
        }
    }

    /// Computes a map from each basic block to its immediate dominator, with the entry mapping to itself.
    pub fn compute_dominator_tree(&self, ctx: &Context) -> FxHashMap<Ptr<BasicBlock>, Ptr<BasicBlock>> {
        // An implementation of the algorithm from page 7 of "A Simple, Fast Dominance Algorithm" by Cooper et. al.
        if self.blocks.first == None {
            return FxHashMap::default()
        };

        let rpo = graph::traversals::region::topological_order(ctx, self.self_ptr);
        let rpo_index: FxHashMap<Ptr<BasicBlock>, usize> = rpo.iter()
            .enumerate()
            .map(|(i, &block)| (block, i))
            .collect();

        const ALL: usize = usize::MAX;
        let mut dom = vec![ALL; rpo.len()];
        dom[0] = 0;

        fn intersect(a: usize, b: usize, dom: &[usize]) -> usize {
            if a == b { return a };
            if a > b { return intersect(dom[a],b,&dom) };
            return intersect(a, dom[b], &dom);
        }

        loop {
            let mut changed = false;

            for (i, &block) in rpo.iter().enumerate().skip(1) {
                let mut new_dom = ALL;
                for pred in block.preds(ctx) {
                    let pred_idx = rpo_index[&pred];
                    if dom[pred_idx] != ALL {
                        if new_dom == ALL {
                            new_dom = pred_idx;
                        } else {
                            new_dom = intersect(new_dom, pred_idx, &dom);
                        }
                    }
                }
                if dom[i] != new_dom {
                    dom[i] = new_dom;
                    changed = true;
                }
            }

            if !changed {
                break;
            }
        }

        rpo.iter()
            .enumerate()
            .map(|(i, &block)| (block, rpo[dom[i]]))
            .collect()
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
    fn get_arena(ctx: &Context) -> &crate::context::Arena<Self> {
        &ctx.regions
    }

    fn get_arena_mut(ctx: &mut Context) -> &mut crate::context::Arena<Self> {
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
            fmt_iter(
                self.iter(ctx),
                ctx,
                state,
                ListSeparator::CharNewline('\n'),
                f,
            )?;
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
            .enter_region(state_stream.state.ctx, parent_op)?;

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

        // If the parsing failed, there may be unresolved references,
        // and `exit_region` will flag those, thus masking the real error.
        // So we ignore any errors from `exit_region` itself.
        if result.is_err() {
            let _ =
                state_stream
                    .state
                    .name_tracker
                    .exit_region(state_stream.state.ctx, parent_op, loc);
            return result.into();
        }

        state_stream
            .state
            .name_tracker
            .exit_region(state_stream.state.ctx, parent_op, loc)?;

        result.into()
    }
}

#[cfg(test)]
mod tests {
    use pliron::derive::pliron_op;

    use crate::{
        basic_block::BasicBlock,
        builtin::{
            op_interfaces::{IsTerminatorInterface, NResultsInterface, OneRegionInterface},
            ops::FuncOp,
            types::FunctionType,
        },
        context::Context,
        linked_list::ContainsLinkedList,
        op::Op,
        operation::Operation,
    };

    #[pliron_op(
        name = "test.br",
        format = "",
        interfaces = [IsTerminatorInterface, NResultsInterface<0>],
        verifier = "succ",
    )]
    struct BrOp;
    impl BrOp {
        fn new(ctx: &mut Context, dest: crate::context::Ptr<BasicBlock>) -> Self {
            BrOp {
                op: Operation::new(
                    ctx,
                    Self::get_concrete_op_info(),
                    vec![],
                    vec![],
                    vec![dest],
                    0,
                ),
            }
        }
    }

    #[pliron_op(
        name = "test.cond_br",
        format = "",
        interfaces = [IsTerminatorInterface, NResultsInterface<0>],
        verifier = "succ",
    )]
    struct CondBrOp;
    impl CondBrOp {
        fn new(
            ctx: &mut Context,
            true_dest: crate::context::Ptr<BasicBlock>,
            false_dest: crate::context::Ptr<BasicBlock>,
        ) -> Self {
            CondBrOp {
                op: Operation::new(
                    ctx,
                    Self::get_concrete_op_info(),
                    vec![],
                    vec![],
                    vec![true_dest, false_dest],
                    0,
                ),
            }
        }
    }

    #[pliron_op(
        name = "test.tri_br",
        format = "",
        interfaces = [IsTerminatorInterface, NResultsInterface<0>],
        verifier = "succ",
    )]
    struct TriBrOp;
    impl TriBrOp {
        fn new(
            ctx: &mut Context,
            a: crate::context::Ptr<BasicBlock>,
            b: crate::context::Ptr<BasicBlock>,
            c: crate::context::Ptr<BasicBlock>,
        ) -> Self {
            TriBrOp {
                op: Operation::new(
                    ctx,
                    Self::get_concrete_op_info(),
                    vec![],
                    vec![],
                    vec![a, b, c],
                    0,
                ),
            }
        }
    }

    #[pliron_op(
        name = "test.halt",
        format = "",
        interfaces = [IsTerminatorInterface, NResultsInterface<0>],
        verifier = "succ",
    )]
    struct HaltOp;
    impl HaltOp {
        fn new(ctx: &mut Context) -> Self {
            HaltOp {
                op: Operation::new(
                    ctx,
                    Self::get_concrete_op_info(),
                    vec![],
                    vec![],
                    vec![],
                    0,
                ),
            }
        }
    }

    /// Create a FuncOp with an empty function type and return its region + entry block.
    fn make_func(
        ctx: &mut Context,
    ) -> (
        crate::context::Ptr<crate::region::Region>,
        crate::context::Ptr<BasicBlock>,
    ) {
        let func_ty = FunctionType::get(ctx, vec![], vec![]);
        let func = FuncOp::new(ctx, "test_func".try_into().unwrap(), func_ty);
        let region = func.get_region(ctx);
        let entry = region.deref(ctx).get_head().unwrap();
        (region, entry)
    }

    #[test]
    fn dominator_tree_single_block() {
        let ctx = &mut Context::new();
        let (region, entry) = make_func(ctx);

        HaltOp::new(ctx).get_operation().insert_at_back(entry, ctx);

        let idom = region.deref(ctx).compute_dominator_tree(ctx);
        assert_eq!(idom.len(), 1);
        assert_eq!(idom[&entry], entry);
    }

    #[test]
    fn dominator_tree_linear_chain() {
        // entry -> a -> b
        let ctx = &mut Context::new();
        let (region, entry) = make_func(ctx);

        let a = BasicBlock::new(ctx, Some("a".try_into().unwrap()), vec![]);
        let b = BasicBlock::new(ctx, Some("b".try_into().unwrap()), vec![]);
        a.insert_at_back(region, ctx);
        b.insert_at_back(region, ctx);

        BrOp::new(ctx, a).get_operation().insert_at_back(entry, ctx);
        BrOp::new(ctx, b).get_operation().insert_at_back(a, ctx);
        HaltOp::new(ctx).get_operation().insert_at_back(b, ctx);

        let idom = region.deref(ctx).compute_dominator_tree(ctx);
        assert_eq!(idom.len(), 3);
        assert_eq!(idom[&entry], entry);
        assert_eq!(idom[&a], entry);
        assert_eq!(idom[&b], a);
    }

    #[test]
    fn dominator_tree_diamond() {
        //        entry
        //       /     \
        //    then    else
        //       \     /
        //        merge
        let ctx = &mut Context::new();
        let (region, entry) = make_func(ctx);

        let then_bb = BasicBlock::new(ctx, Some("then".try_into().unwrap()), vec![]);
        let else_bb = BasicBlock::new(ctx, Some("else".try_into().unwrap()), vec![]);
        let merge = BasicBlock::new(ctx, Some("merge".try_into().unwrap()), vec![]);
        then_bb.insert_at_back(region, ctx);
        else_bb.insert_at_back(region, ctx);
        merge.insert_at_back(region, ctx);

        CondBrOp::new(ctx, then_bb, else_bb)
            .get_operation()
            .insert_at_back(entry, ctx);
        BrOp::new(ctx, merge)
            .get_operation()
            .insert_at_back(then_bb, ctx);
        BrOp::new(ctx, merge)
            .get_operation()
            .insert_at_back(else_bb, ctx);
        HaltOp::new(ctx).get_operation().insert_at_back(merge, ctx);

        let dom = region.deref(ctx).compute_dominator_tree(ctx);
        assert_eq!(dom.len(), 4);
        assert_eq!(dom[&entry], entry);
        assert_eq!(dom[&then_bb], entry);
        assert_eq!(dom[&else_bb], entry);
        assert_eq!(dom[&merge], entry);
    }

    #[test]
    fn dominator_tree_loop() {
        //              +--------+
        //              v        |
        //  entry -> header -> body
        //              |
        //              v
        //             exit
        let ctx = &mut Context::new();
        let (region, entry) = make_func(ctx);

        let header = BasicBlock::new(ctx, Some("header".try_into().unwrap()), vec![]);
        let body = BasicBlock::new(ctx, Some("body".try_into().unwrap()), vec![]);
        let exit = BasicBlock::new(ctx, Some("exit".try_into().unwrap()), vec![]);
        header.insert_at_back(region, ctx);
        body.insert_at_back(region, ctx);
        exit.insert_at_back(region, ctx);

        BrOp::new(ctx, header)
            .get_operation()
            .insert_at_back(entry, ctx);
        CondBrOp::new(ctx, body, exit)
            .get_operation()
            .insert_at_back(header, ctx);
        BrOp::new(ctx, header)
            .get_operation()
            .insert_at_back(body, ctx);
        HaltOp::new(ctx).get_operation().insert_at_back(exit, ctx);

        let dom = region.deref(ctx).compute_dominator_tree(ctx);
        assert_eq!(dom.len(), 4);
        assert_eq!(dom[&entry], entry);
        assert_eq!(dom[&header], entry);
        assert_eq!(dom[&body], header);
        assert_eq!(dom[&exit], header);
    }

    #[test]
    fn dominator_tree_cooper_fig4() {
        // From the paper "A Simple, Fast Dominance Algorithm" by Cooper et. al.

        //           ┌───────┐
        //           │ entry │
        //           └───────┘
        //            /     \
        //           v       v
        //        ┌───┐   ┌───┐
        //        │ 5 │   │ 4 │
        //        └───┘   └───┘
        //          |      | \
        //          v      v  v
        //        ┌───┐ ┌───┐ ┌───┐
        //        │ 1 │⇄│ 2 │⇄│ 3 │
        //        └───┘ └───┘ └───┘
        let ctx = &mut Context::new();
        let (region, entry) = make_func(ctx);

        let five = BasicBlock::new(ctx, Some("five".try_into().unwrap()), vec![]);
        let four = BasicBlock::new(ctx, Some("four".try_into().unwrap()), vec![]);
        let three = BasicBlock::new(ctx, Some("three".try_into().unwrap()), vec![]);
        let two = BasicBlock::new(ctx, Some("two".try_into().unwrap()), vec![]);
        let one = BasicBlock::new(ctx, Some("one".try_into().unwrap()), vec![]);
        five.insert_at_back(region, ctx);
        four.insert_at_back(region, ctx);
        three.insert_at_back(region, ctx);
        two.insert_at_back(region, ctx);
        one.insert_at_back(region, ctx);

        // entry -> five, four
        CondBrOp::new(ctx, five, four)
            .get_operation()
            .insert_at_back(entry, ctx);
        // five -> one
        BrOp::new(ctx, one)
            .get_operation()
            .insert_at_back(five, ctx);
        // four -> two, three
        CondBrOp::new(ctx, two, three)
            .get_operation()
            .insert_at_back(four, ctx);
        // one -> two
        BrOp::new(ctx, two)
            .get_operation()
            .insert_at_back(one, ctx);
        // two -> one, three
        CondBrOp::new(ctx, one, three)
            .get_operation()
            .insert_at_back(two, ctx);
        // three -> two
        BrOp::new(ctx, two)
            .get_operation()
            .insert_at_back(three, ctx);

        let dom = region.deref(ctx).compute_dominator_tree(ctx);
        assert_eq!(dom.len(), 6);
        assert_eq!(dom[&entry], entry);
        assert_eq!(dom[&five], entry);
        assert_eq!(dom[&four], entry);
        assert_eq!(dom[&one], entry);
        assert_eq!(dom[&two], entry);
        assert_eq!(dom[&three], entry);
    }

    #[test]
    fn dominator_tree_dragon() {
        // From the dragon book, second edition, pg 657

        let ctx = &mut Context::new();
        let (region, n1) = make_func(ctx);

        let n2 = BasicBlock::new(ctx, Some("n2".try_into().unwrap()), vec![]);
        let n3 = BasicBlock::new(ctx, Some("n3".try_into().unwrap()), vec![]);
        let n4 = BasicBlock::new(ctx, Some("n4".try_into().unwrap()), vec![]);
        let n5 = BasicBlock::new(ctx, Some("n5".try_into().unwrap()), vec![]);
        let n6 = BasicBlock::new(ctx, Some("n6".try_into().unwrap()), vec![]);
        let n7 = BasicBlock::new(ctx, Some("n7".try_into().unwrap()), vec![]);
        let n8 = BasicBlock::new(ctx, Some("n8".try_into().unwrap()), vec![]);
        let n9 = BasicBlock::new(ctx, Some("n9".try_into().unwrap()), vec![]);
        let n10 = BasicBlock::new(ctx, Some("n10".try_into().unwrap()), vec![]);
        n2.insert_at_back(region, ctx);
        n3.insert_at_back(region, ctx);
        n4.insert_at_back(region, ctx);
        n5.insert_at_back(region, ctx);
        n6.insert_at_back(region, ctx);
        n7.insert_at_back(region, ctx);
        n8.insert_at_back(region, ctx);
        n9.insert_at_back(region, ctx);
        n10.insert_at_back(region, ctx);

        // 1 -> 2, 3
        CondBrOp::new(ctx, n2, n3)
            .get_operation()
            .insert_at_back(n1, ctx);
        // 2 -> 3
        BrOp::new(ctx, n3)
            .get_operation()
            .insert_at_back(n2, ctx);
        // 3 -> 4
        BrOp::new(ctx, n4)
            .get_operation()
            .insert_at_back(n3, ctx);
        // 4 -> 5, 6, 3
        TriBrOp::new(ctx, n5, n6, n3)
            .get_operation()
            .insert_at_back(n4, ctx);
        // 5 -> 7
        BrOp::new(ctx, n7)
            .get_operation()
            .insert_at_back(n5, ctx);
        // 6 -> 7
        BrOp::new(ctx, n7)
            .get_operation()
            .insert_at_back(n6, ctx);
        // 7 -> 4, 8
        CondBrOp::new(ctx, n4, n8)
            .get_operation()
            .insert_at_back(n7, ctx);
        // 8 -> 9, 10, 3
        TriBrOp::new(ctx, n9, n10, n3)
            .get_operation()
            .insert_at_back(n8, ctx);
        // 9 -> 1
        BrOp::new(ctx, n1)
            .get_operation()
            .insert_at_back(n9, ctx);
        // 10 -> 7
        BrOp::new(ctx, n7)
            .get_operation()
            .insert_at_back(n10, ctx);

        let dom = region.deref(ctx).compute_dominator_tree(ctx);
        assert_eq!(dom.len(), 10);
        assert_eq!(dom[&n1], n1);
        assert_eq!(dom[&n2], n1);
        assert_eq!(dom[&n3], n1);
        assert_eq!(dom[&n4], n3);
        assert_eq!(dom[&n5], n4);
        assert_eq!(dom[&n6], n4);
        assert_eq!(dom[&n7], n4);
        assert_eq!(dom[&n8], n7);
        assert_eq!(dom[&n9], n8);
        assert_eq!(dom[&n10], n8);
    }

    #[test]
    fn dominator_tree_empty_region() {
        let ctx = &mut Context::new();
        let func_ty = FunctionType::get(ctx, vec![], vec![]);
        let func = FuncOp::new(ctx, "empty_func".try_into().unwrap(), func_ty);
        let region = func.get_region(ctx);

        let entry = region.deref(ctx).get_head().unwrap();
        entry.unlink(ctx);

        let dom = region.deref(ctx).compute_dominator_tree(ctx);
        assert!(dom.is_empty());
    }
}
