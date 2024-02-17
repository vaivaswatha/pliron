use std::{marker::PhantomData, ops::ControlFlow};

use crate::{
    basic_block::BasicBlock,
    context::{Context, Ptr},
    linked_list::ContainsLinkedList,
    operation::Operation,
    region::Region,
};

pub type WalkResult<B> = ControlFlow<B, WalkCont>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WalkCont {
    Advance, // Advance the walk
    Skip,    // Advance to the next sibling
}

pub fn walk_op<B, O: Order, S: Strategy>(
    root_op: Ptr<Operation>,
    ctx: &Context,
    callback: &mut impl FnMut(&Context, Ptr<Operation>) -> WalkResult<B>,
) -> WalkResult<B> {
    let cb = Callback(callback, PhantomData);
    let mut acceptor = O::build::<B, S, _>(cb);
    acceptor.accept_op(ctx, root_op)
}

pub fn walk_op_mut<B, O: OrderMut, S: StrategyMut>(
    root_op: Ptr<Operation>,
    ctx: &mut Context,
    callback: &mut impl FnMut(&mut Context, Ptr<Operation>) -> WalkResult<B>,
) -> WalkResult<B> {
    let cb = CallbackMut(callback, PhantomData);
    let mut acceptor = O::build_mut::<B, S, _>(cb);
    acceptor.accept_op_mut(ctx, root_op)
}

pub fn walk_regions<B, O: Order, S: Strategy>(
    root_op: Ptr<Operation>,
    ctx: &Context,
    callback: &mut impl FnMut(&Context, Ptr<Region>) -> WalkResult<B>,
) -> WalkResult<B> {
    let cb = Callback(callback, PhantomData);
    let mut acceptor = O::build::<B, S, _>(cb);
    acceptor.accept_op(ctx, root_op)
}

pub fn walk_regions_mut<B, O: OrderMut, S: StrategyMut>(
    root_op: Ptr<Operation>,
    ctx: &mut Context,
    callback: &mut impl FnMut(&mut Context, Ptr<Region>) -> WalkResult<B>,
) -> WalkResult<B> {
    let cb = CallbackMut(callback, PhantomData);
    let mut acceptor = O::build_mut::<B, S, _>(cb);
    acceptor.accept_op_mut(ctx, root_op)
}

pub fn walk_blocks<B, O: Order, S: Strategy>(
    root_op: Ptr<Operation>,
    ctx: &Context,
    callback: &mut impl FnMut(&Context, Ptr<BasicBlock>) -> WalkResult<B>,
) -> WalkResult<B> {
    let cb = Callback(callback, PhantomData);
    let mut acceptor = O::build::<B, S, _>(cb);
    acceptor.accept_op(ctx, root_op)
}

pub fn walk_blocks_mut<B, O: OrderMut, S: StrategyMut>(
    root_op: Ptr<Operation>,
    ctx: &mut Context,
    callback: &mut impl FnMut(&mut Context, Ptr<BasicBlock>) -> WalkResult<B>,
) -> WalkResult<B> {
    let cb = CallbackMut(callback, PhantomData);
    let mut acceptor = O::build_mut::<B, S, _>(cb);
    acceptor.accept_op_mut(ctx, root_op)
}

struct Callback<B, IR, F: FnMut(&Context, Ptr<IR>) -> WalkResult<B>>(F, PhantomData<IR>);

impl<B, F: FnMut(&Context, Ptr<Operation>) -> WalkResult<B>> Visitor<B>
    for Callback<B, Operation, F>
{
    fn visit_op(&mut self, ctx: &Context, op: Ptr<Operation>) -> WalkResult<B> {
        (self.0)(ctx, op)
    }
}

impl<B, F: FnMut(&Context, Ptr<Region>) -> WalkResult<B>> Visitor<B> for Callback<B, Region, F> {
    fn visit_region(&mut self, ctx: &Context, region: Ptr<Region>) -> WalkResult<B> {
        (self.0)(ctx, region)
    }
}

impl<B, F: FnMut(&Context, Ptr<BasicBlock>) -> WalkResult<B>> Visitor<B>
    for Callback<B, BasicBlock, F>
{
    fn visit_block(&mut self, ctx: &Context, block: Ptr<BasicBlock>) -> WalkResult<B> {
        (self.0)(ctx, block)
    }
}

struct CallbackMut<B, IR, F: FnMut(&mut Context, Ptr<IR>) -> WalkResult<B>>(F, PhantomData<IR>);

impl<B, F: FnMut(&mut Context, Ptr<Operation>) -> WalkResult<B>> VisitorMut<B>
    for CallbackMut<B, Operation, F>
{
    fn visit_op_mut(&mut self, ctx: &mut Context, op: Ptr<Operation>) -> WalkResult<B> {
        (self.0)(ctx, op)
    }
}

impl<B, F: FnMut(&mut Context, Ptr<Region>) -> WalkResult<B>> VisitorMut<B>
    for CallbackMut<B, Region, F>
{
    fn visit_region_mut(&mut self, ctx: &mut Context, region: Ptr<Region>) -> WalkResult<B> {
        (self.0)(ctx, region)
    }
}

impl<B, F: FnMut(&mut Context, Ptr<BasicBlock>) -> WalkResult<B>> VisitorMut<B>
    for CallbackMut<B, BasicBlock, F>
{
    fn visit_block_mut(&mut self, ctx: &mut Context, block: Ptr<BasicBlock>) -> WalkResult<B> {
        (self.0)(ctx, block)
    }
}

// ---------------------------------------------------------------------------------------------

pub trait Acceptor<B> {
    fn accept_op(&mut self, ctx: &Context, op: Ptr<Operation>) -> WalkResult<B> {
        Forward::walk_regions(self, ctx, op)
    }

    fn accept_region(&mut self, ctx: &Context, region: Ptr<Region>) -> WalkResult<B> {
        Forward::walk_blocks(self, ctx, region)
    }

    fn accept_block(&mut self, ctx: &Context, block: Ptr<BasicBlock>) -> WalkResult<B> {
        Forward::walk_ops(self, ctx, block)
    }
}

pub trait AcceptorMut<B> {
    fn accept_op_mut(&mut self, ctx: &mut Context, op: Ptr<Operation>) -> WalkResult<B> {
        Forward::walk_regions_mut(self, ctx, op)
    }

    fn accept_region_mut(&mut self, ctx: &mut Context, region: Ptr<Region>) -> WalkResult<B> {
        Forward::walk_blocks_mut(self, ctx, region)
    }

    fn accept_block_mut(&mut self, ctx: &mut Context, block: Ptr<BasicBlock>) -> WalkResult<B> {
        Forward::walk_ops_mut(self, ctx, block)
    }
}

pub trait Order {
    type Acceptor<B, S: Strategy, V: Visitor<B>>: Acceptor<B>;

    fn build<B, S: Strategy, V: Visitor<B>>(v: V) -> Self::Acceptor<B, S, V>;
}

pub trait OrderMut {
    type AcceptorMut<B, S: StrategyMut, V: VisitorMut<B>>: AcceptorMut<B>;

    fn build_mut<B, S: StrategyMut, V: VisitorMut<B>>(v: V) -> Self::AcceptorMut<B, S, V>;
}

pub struct PreOrder;

impl Order for PreOrder {
    type Acceptor<B, S: Strategy, V: Visitor<B>> = PreOrderAcceptor<B, S, V>;

    fn build<B, S: Strategy, V: Visitor<B>>(v: V) -> PreOrderAcceptor<B, S, V> {
        PreOrderAcceptor(v, PhantomData)
    }
}

impl OrderMut for PreOrder {
    type AcceptorMut<B, S: StrategyMut, V: VisitorMut<B>> = PreOrderAcceptor<B, S, V>;

    fn build_mut<B, S: StrategyMut, V: VisitorMut<B>>(v: V) -> PreOrderAcceptor<B, S, V> {
        PreOrderAcceptor(v, PhantomData)
    }
}

pub struct PreOrderAcceptor<B, S, V>(V, PhantomData<(S, B)>);

impl<B, S: Strategy, V: Visitor<B>> Acceptor<B> for PreOrderAcceptor<B, S, V> {
    fn accept_op(&mut self, ctx: &Context, op: Ptr<Operation>) -> WalkResult<B> {
        let c = self.0.visit_op(ctx, op)?;
        if c == WalkCont::Advance {
            S::walk_regions(self, ctx, op)?;
        }
        WalkResult::Continue(WalkCont::Advance)
    }

    fn accept_region(&mut self, ctx: &Context, region: Ptr<Region>) -> WalkResult<B> {
        let c = self.0.visit_region(ctx, region)?;
        if c == WalkCont::Advance {
            S::walk_blocks(self, ctx, region)?;
        }
        WalkResult::Continue(WalkCont::Advance)
    }

    fn accept_block(&mut self, ctx: &Context, block: Ptr<BasicBlock>) -> WalkResult<B> {
        let c = self.0.visit_block(ctx, block)?;
        if c == WalkCont::Advance {
            S::walk_ops(self, ctx, block)?;
        }
        WalkResult::Continue(WalkCont::Advance)
    }
}

impl<B, S: StrategyMut, V: VisitorMut<B>> AcceptorMut<B> for PreOrderAcceptor<B, S, V> {
    fn accept_op_mut(&mut self, ctx: &mut Context, op: Ptr<Operation>) -> WalkResult<B> {
        let c = self.0.visit_op_mut(ctx, op)?;
        if c == WalkCont::Advance {
            S::walk_regions_mut(self, ctx, op)?;
        }
        WalkResult::Continue(WalkCont::Advance)
    }

    fn accept_region_mut(&mut self, ctx: &mut Context, region: Ptr<Region>) -> WalkResult<B> {
        let c = self.0.visit_region_mut(ctx, region)?;
        if c == WalkCont::Advance {
            S::walk_blocks_mut(self, ctx, region)?;
        }
        WalkResult::Continue(WalkCont::Advance)
    }

    fn accept_block_mut(&mut self, ctx: &mut Context, block: Ptr<BasicBlock>) -> WalkResult<B> {
        let c = self.0.visit_block_mut(ctx, block)?;
        if c == WalkCont::Advance {
            S::walk_ops_mut(self, ctx, block)?;
        }
        WalkResult::Continue(WalkCont::Advance)
    }
}

struct PostOrder;

impl Order for PostOrder {
    type Acceptor<B, S: Strategy, V: Visitor<B>> = PostOrderAcceptor<B, S, V>;

    fn build<B, S: Strategy, V: Visitor<B>>(v: V) -> PostOrderAcceptor<B, S, V> {
        PostOrderAcceptor(v, PhantomData)
    }
}

struct PostOrderAcceptor<B, S, V>(V, PhantomData<(S, B)>);

impl<B, S: Strategy, V: Visitor<B>> Acceptor<B> for PostOrderAcceptor<B, S, V> {
    fn accept_op(&mut self, ctx: &Context, op: Ptr<Operation>) -> WalkResult<B> {
        S::walk_regions(self, ctx, op)?;
        self.0.visit_op(ctx, op)
    }

    fn accept_region(&mut self, ctx: &Context, region: Ptr<Region>) -> WalkResult<B> {
        S::walk_blocks(self, ctx, region)?;
        self.0.visit_region(ctx, region)
    }

    fn accept_block(&mut self, ctx: &Context, block: Ptr<BasicBlock>) -> WalkResult<B> {
        S::walk_ops(self, ctx, block)?;
        self.0.visit_block(ctx, block)
    }
}

impl<B, S: StrategyMut, V: Visitor<B>> AcceptorMut<B> for PostOrderAcceptor<B, S, V> {
    fn accept_op_mut(&mut self, ctx: &mut Context, op: Ptr<Operation>) -> WalkResult<B> {
        S::walk_regions_mut(self, ctx, op)?;
        self.0.visit_op(ctx, op)
    }

    fn accept_region_mut(&mut self, ctx: &mut Context, region: Ptr<Region>) -> WalkResult<B> {
        S::walk_blocks_mut(self, ctx, region)?;
        self.0.visit_region(ctx, region)
    }

    fn accept_block_mut(&mut self, ctx: &mut Context, block: Ptr<BasicBlock>) -> WalkResult<B> {
        S::walk_ops_mut(self, ctx, block)?;
        self.0.visit_block(ctx, block)
    }
}

struct EnterExit<B, S, V>(V, PhantomData<(S, B)>);

impl<B, S: Strategy, V: SurroundingVisitor<B>> Acceptor<B> for EnterExit<B, S, V> {
    fn accept_op(&mut self, ctx: &Context, op: Ptr<Operation>) -> WalkResult<B> {
        let c = self.0.enter_op(ctx, op)?;
        if c == WalkCont::Advance {
            S::walk_regions(self, ctx, op)?;
        }
        self.0.exit_op(ctx, op)
    }

    fn accept_region(&mut self, ctx: &Context, region: Ptr<Region>) -> WalkResult<B> {
        let c = self.0.enter_region(ctx, region)?;
        if c == WalkCont::Advance {
            S::walk_blocks(self, ctx, region)?;
        }
        self.0.exit_region(ctx, region)
    }

    fn accept_block(&mut self, ctx: &Context, block: Ptr<BasicBlock>) -> WalkResult<B> {
        let c = self.0.enter_block(ctx, block)?;
        if c == WalkCont::Advance {
            S::walk_ops(self, ctx, block)?;
        }
        self.0.exit_block(ctx, block)
    }
}

impl<B, S: StrategyMut, V: SurroundingVisitorMut<B>> AcceptorMut<B> for EnterExit<B, S, V> {
    fn accept_op_mut(&mut self, ctx: &mut Context, op: Ptr<Operation>) -> WalkResult<B> {
        let c = self.0.enter_op_mut(ctx, op)?;
        if c == WalkCont::Advance {
            S::walk_regions_mut(self, ctx, op)?;
        }
        self.0.exit_op_mut(ctx, op)
    }

    fn accept_region_mut(&mut self, ctx: &mut Context, region: Ptr<Region>) -> WalkResult<B> {
        let c = self.0.enter_region_mut(ctx, region)?;
        if c == WalkCont::Advance {
            S::walk_blocks_mut(self, ctx, region)?;
        }
        self.0.exit_region_mut(ctx, region)
    }

    fn accept_block_mut(&mut self, ctx: &mut Context, block: Ptr<BasicBlock>) -> WalkResult<B> {
        let c = self.0.enter_block_mut(ctx, block)?;
        if c == WalkCont::Advance {
            S::walk_ops_mut(self, ctx, block)?;
        }
        self.0.exit_block_mut(ctx, block)
    }
}

pub trait Strategy {
    fn walk_regions<A, B>(a: &mut A, ctx: &Context, op: Ptr<Operation>) -> WalkResult<B>
    where
        A: Acceptor<B> + ?Sized;

    fn walk_blocks<A, B>(a: &mut A, ctx: &Context, region: Ptr<Region>) -> WalkResult<B>
    where
        A: Acceptor<B> + ?Sized;

    fn walk_ops<A, B>(a: &mut A, ctx: &Context, block: Ptr<BasicBlock>) -> WalkResult<B>
    where
        A: Acceptor<B> + ?Sized;
}

pub trait StrategyMut {
    fn walk_regions_mut<A, B>(a: &mut A, ctx: &mut Context, op: Ptr<Operation>) -> WalkResult<B>
    where
        A: AcceptorMut<B> + ?Sized;

    fn walk_blocks_mut<A, B>(a: &mut A, ctx: &mut Context, region: Ptr<Region>) -> WalkResult<B>
    where
        A: AcceptorMut<B> + ?Sized;

    fn walk_ops_mut<A, B>(a: &mut A, ctx: &mut Context, block: Ptr<BasicBlock>) -> WalkResult<B>
    where
        A: AcceptorMut<B> + ?Sized;
}

struct Forward;

impl Strategy for Forward {
    fn walk_regions<A, B>(a: &mut A, ctx: &Context, op: Ptr<Operation>) -> WalkResult<B>
    where
        A: Acceptor<B> + ?Sized,
    {
        for ptr in op.deref(ctx).regions().iter().cloned() {
            a.accept_region(ctx, ptr)?;
        }
        WalkResult::Continue(WalkCont::Advance)
    }

    fn walk_blocks<A, B>(a: &mut A, ctx: &Context, region: Ptr<Region>) -> WalkResult<B>
    where
        A: Acceptor<B> + ?Sized,
    {
        for ptr in region.deref(ctx).iter(ctx) {
            a.accept_block(ctx, ptr)?;
        }
        WalkResult::Continue(WalkCont::Advance)
    }

    fn walk_ops<A, B>(a: &mut A, ctx: &Context, block: Ptr<BasicBlock>) -> WalkResult<B>
    where
        A: Acceptor<B> + ?Sized,
    {
        for ptr in block.deref(ctx).iter(ctx) {
            a.accept_op(ctx, ptr)?;
        }
        WalkResult::Continue(WalkCont::Advance)
    }
}

impl StrategyMut for Forward {
    fn walk_regions_mut<A, B>(a: &mut A, ctx: &mut Context, op: Ptr<Operation>) -> WalkResult<B>
    where
        A: AcceptorMut<B> + ?Sized,
    {
        let iter = {
            let op = op.deref(ctx);
            op.regions().iter().cloned().collect::<Vec<_>>()
        };
        for ptr in iter {
            a.accept_region_mut(ctx, ptr)?;
        }
        WalkResult::Continue(WalkCont::Advance)
    }

    fn walk_blocks_mut<A, B>(a: &mut A, ctx: &mut Context, region: Ptr<Region>) -> WalkResult<B>
    where
        A: AcceptorMut<B> + ?Sized,
    {
        let iter = {
            let region: &Region = &region.deref(ctx);
            region.iter(ctx).collect::<Vec<_>>()
        };
        for ptr in iter {
            a.accept_block_mut(ctx, ptr)?;
        }
        WalkResult::Continue(WalkCont::Advance)
    }

    fn walk_ops_mut<A, B>(a: &mut A, ctx: &mut Context, block: Ptr<BasicBlock>) -> WalkResult<B>
    where
        A: AcceptorMut<B> + ?Sized,
    {
        let iter = {
            let block: &BasicBlock = &block.deref(ctx);
            block.iter(ctx).collect::<Vec<_>>()
        };
        for ptr in iter {
            a.accept_op_mut(ctx, ptr)?;
        }
        WalkResult::Continue(WalkCont::Advance)
    }
}

struct Reverse;

impl Strategy for Reverse {
    fn walk_regions<A, B>(a: &mut A, ctx: &Context, op: Ptr<Operation>) -> WalkResult<B>
    where
        A: Acceptor<B> + ?Sized,
    {
        for ptr in op.deref(ctx).regions().iter().cloned().rev() {
            a.accept_region(ctx, ptr)?;
        }
        WalkResult::Continue(WalkCont::Advance)
    }

    fn walk_blocks<A, B>(a: &mut A, ctx: &Context, region: Ptr<Region>) -> WalkResult<B>
    where
        A: Acceptor<B> + ?Sized,
    {
        for ptr in region.deref(ctx).iter(ctx).rev() {
            a.accept_block(ctx, ptr)?;
        }
        WalkResult::Continue(WalkCont::Advance)
    }

    fn walk_ops<A, B>(a: &mut A, ctx: &Context, block: Ptr<BasicBlock>) -> WalkResult<B>
    where
        A: Acceptor<B> + ?Sized,
    {
        for ptr in block.deref(ctx).iter(ctx).rev() {
            a.accept_op(ctx, ptr)?;
        }
        WalkResult::Continue(WalkCont::Advance)
    }
}

impl StrategyMut for Reverse {
    fn walk_regions_mut<A, B>(a: &mut A, ctx: &mut Context, op: Ptr<Operation>) -> WalkResult<B>
    where
        A: AcceptorMut<B> + ?Sized,
    {
        let regions = {
            let op = op.deref(ctx);
            op.regions().iter().cloned().collect::<Vec<_>>()
        };
        for ptr in regions.into_iter().rev() {
            a.accept_region_mut(ctx, ptr)?;
        }
        WalkResult::Continue(WalkCont::Advance)
    }

    fn walk_blocks_mut<A, B>(a: &mut A, ctx: &mut Context, region: Ptr<Region>) -> WalkResult<B>
    where
        A: AcceptorMut<B> + ?Sized,
    {
        let blocks = {
            let region: &Region = &region.deref(ctx);
            region.iter(ctx).collect::<Vec<_>>()
        };
        for ptr in blocks.into_iter().rev() {
            a.accept_block_mut(ctx, ptr)?;
        }
        WalkResult::Continue(WalkCont::Advance)
    }

    fn walk_ops_mut<A, B>(a: &mut A, ctx: &mut Context, block: Ptr<BasicBlock>) -> WalkResult<B>
    where
        A: AcceptorMut<B> + ?Sized,
    {
        let ops = {
            let block: &BasicBlock = &block.deref(ctx);
            block.iter(ctx).collect::<Vec<_>>()
        };
        for ptr in ops.into_iter().rev() {
            a.accept_op_mut(ctx, ptr)?;
        }
        WalkResult::Continue(WalkCont::Advance)
    }
}

pub trait Visitor<B> {
    fn visit_op(&mut self, _ctx: &Context, _op: Ptr<Operation>) -> WalkResult<B> {
        WalkResult::Continue(WalkCont::Advance)
    }

    fn visit_region(&mut self, _ctx: &Context, _region: Ptr<Region>) -> WalkResult<B> {
        WalkResult::Continue(WalkCont::Advance)
    }

    fn visit_block(&mut self, _ctx: &Context, _block: Ptr<BasicBlock>) -> WalkResult<B> {
        WalkResult::Continue(WalkCont::Advance)
    }
}

pub trait VisitorMut<B> {
    fn visit_op_mut(&mut self, _ctx: &mut Context, _op: Ptr<Operation>) -> WalkResult<B> {
        WalkResult::Continue(WalkCont::Advance)
    }

    fn visit_region_mut(&mut self, _ctx: &mut Context, _region: Ptr<Region>) -> WalkResult<B> {
        WalkResult::Continue(WalkCont::Advance)
    }

    fn visit_block_mut(&mut self, _ctx: &mut Context, _block: Ptr<BasicBlock>) -> WalkResult<B> {
        WalkResult::Continue(WalkCont::Advance)
    }
}

pub trait SurroundingVisitor<B> {
    fn enter_op(&mut self, _ctx: &Context, _op: Ptr<Operation>) -> WalkResult<B> {
        WalkResult::Continue(WalkCont::Advance)
    }

    fn exit_op(&mut self, _ctx: &Context, _op: Ptr<Operation>) -> WalkResult<B> {
        WalkResult::Continue(WalkCont::Advance)
    }

    fn enter_region(&mut self, _ctx: &Context, _region: Ptr<Region>) -> WalkResult<B> {
        WalkResult::Continue(WalkCont::Advance)
    }

    fn exit_region(&mut self, _ctx: &Context, _region: Ptr<Region>) -> WalkResult<B> {
        WalkResult::Continue(WalkCont::Advance)
    }

    fn enter_block(&mut self, _ctx: &Context, _block: Ptr<BasicBlock>) -> WalkResult<B> {
        WalkResult::Continue(WalkCont::Advance)
    }

    fn exit_block(&mut self, _ctx: &Context, _block: Ptr<BasicBlock>) -> WalkResult<B> {
        WalkResult::Continue(WalkCont::Advance)
    }
}

pub trait SurroundingVisitorMut<B> {
    fn enter_op_mut(&mut self, _ctx: &mut Context, _op: Ptr<Operation>) -> WalkResult<B> {
        WalkResult::Continue(WalkCont::Advance)
    }

    fn exit_op_mut(&mut self, _ctx: &mut Context, _op: Ptr<Operation>) -> WalkResult<B> {
        WalkResult::Continue(WalkCont::Advance)
    }

    fn enter_region_mut(&mut self, _ctx: &mut Context, _region: Ptr<Region>) -> WalkResult<B> {
        WalkResult::Continue(WalkCont::Advance)
    }

    fn exit_region_mut(&mut self, _ctx: &mut Context, _region: Ptr<Region>) -> WalkResult<B> {
        WalkResult::Continue(WalkCont::Advance)
    }

    fn enter_block_mut(&mut self, _ctx: &mut Context, _block: Ptr<BasicBlock>) -> WalkResult<B> {
        WalkResult::Continue(WalkCont::Advance)
    }

    fn exit_block_mut(&mut self, _ctx: &mut Context, _block: Ptr<BasicBlock>) -> WalkResult<B> {
        WalkResult::Continue(WalkCont::Advance)
    }
}
