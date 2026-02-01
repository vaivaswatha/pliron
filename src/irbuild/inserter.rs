//! A utility for inserting [Operation]s from a specified insertion point.
//! Similar in spirit to LLVM's IRBuilder, but does not build operations.

use crate::{
    basic_block::BasicBlock,
    common_traits::Named,
    context::{Context, Ptr},
    identifier::Identifier,
    irbuild::listener::InsertionListener,
    op::Op,
    operation::Operation,
    printable::{self, Printable},
    region::Region,
    r#type::TypeObj,
};

/// Insertion point specification for inserting [Operation]s using [IRInserter].
#[derive(Clone, Copy, Default)]
pub enum OpInsertionPoint {
    #[default]
    Unset,
    AtBlockStart(Ptr<BasicBlock>),
    AtBlockEnd(Ptr<BasicBlock>),
    AfterOperation(Ptr<Operation>),
    BeforeOperation(Ptr<Operation>),
}

/// Insertion point specification for insertion [BasicBlock]s using [IRInserter].
#[derive(Clone, Copy, Default)]
pub enum BlockInsertionPoint {
    #[default]
    Unset,
    AtRegionStart(Ptr<Region>),
    AtRegionEnd(Ptr<Region>),
    AfterBlock(Ptr<BasicBlock>),
    BeforeBlock(Ptr<BasicBlock>),
}

impl Printable for OpInsertionPoint {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &printable::State,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        match self {
            OpInsertionPoint::Unset => write!(f, "Op Insertion Point not set"),
            OpInsertionPoint::AtBlockStart(block) => {
                write!(
                    f,
                    "At start of BasicBlock {}",
                    block.deref(ctx).unique_name(ctx)
                )
            }
            OpInsertionPoint::AtBlockEnd(block) => {
                write!(
                    f,
                    "At end of BasicBlock {}",
                    block.deref(ctx).unique_name(ctx)
                )
            }
            OpInsertionPoint::AfterOperation(op) => {
                write!(f, "After Operation {}", op.disp(ctx))
            }
            OpInsertionPoint::BeforeOperation(op) => {
                write!(f, "Before Operation {}", op.disp(ctx))
            }
        }
    }
}

impl Printable for BlockInsertionPoint {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &printable::State,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        match self {
            BlockInsertionPoint::Unset => write!(f, "Block Insertion Point not set"),
            BlockInsertionPoint::AtRegionStart(region) => {
                write!(
                    f,
                    "At start of Region {}",
                    region.deref(ctx).get_index_in_parent(ctx)
                )
            }
            BlockInsertionPoint::AtRegionEnd(region) => {
                write!(
                    f,
                    "At end of Region {}",
                    region.deref(ctx).get_index_in_parent(ctx)
                )
            }
            BlockInsertionPoint::AfterBlock(block) => {
                write!(f, "After BasicBlock {}", block.deref(ctx).unique_name(ctx))
            }
            BlockInsertionPoint::BeforeBlock(block) => {
                write!(f, "Before BasicBlock {}", block.deref(ctx).unique_name(ctx))
            }
        }
    }
}

/// An interface for insertion of IR entities.
/// Use [DummyListener](super::listener::DummyListener) if no listener is needed.
pub trait Inserter<L: InsertionListener>: Default {
    /// Appends an [Operation] at the current insertion point.
    /// The insertion point is updated to be after this newly inserted [Operation].
    fn append_operation(&mut self, ctx: &Context, operation: Ptr<Operation>);

    /// Appends an [Op] at the current insertion point.
    /// The insertion point is updated to be after this newly inserted [Op].
    fn append_op(&mut self, ctx: &Context, op: impl Op);

    /// Inserts an [Operation] at the current insertion point.
    /// To insert a sequence in-order, use [append_operation](Self::append_operation).
    fn insert_operation(&mut self, ctx: &Context, operation: Ptr<Operation>);

    /// Inserts an [Op] at the current insertion point.
    /// To insert a sequence in-order, use [append_op](Self::append_op).
    fn insert_op(&mut self, ctx: &Context, op: impl Op);

    /// Insert [BasicBlock] and the provided insertion point.
    fn insert_block(
        &mut self,
        ctx: &Context,
        insertion_point: BlockInsertionPoint,
        block: Ptr<BasicBlock>,
    );

    /// Create a new [BasicBlock] and insert it before at the provided insertion point.
    /// The internal [OpInsertionPoint] is updated to be at the end of the newly created block.
    fn create_block(
        &mut self,
        ctx: &mut Context,
        insertertion_point: BlockInsertionPoint,
        label: Option<Identifier>,
        arg_types: Vec<Ptr<TypeObj>>,
    ) -> Ptr<BasicBlock>;

    /// Gets the current insertion point.
    fn get_insertion_point(&self) -> OpInsertionPoint;

    /// Is insertion point set?
    fn is_insertion_point_set(&self) -> bool {
        !matches!(self.get_insertion_point(), OpInsertionPoint::Unset)
    }

    /// Get the current insertion block.
    fn get_insertion_block(&self, ctx: &Context) -> Ptr<BasicBlock>;

    /// Set the insertion point.
    fn set_insertion_point(&mut self, point: OpInsertionPoint);

    /// Sets the insertion point to the start of the given block.
    fn set_insertion_point_to_block_start(&mut self, block: Ptr<BasicBlock>) {
        self.set_insertion_point(OpInsertionPoint::AtBlockStart(block));
    }

    /// Sets the insertion point to the end of the given block.
    fn set_insertion_point_to_block_end(&mut self, block: Ptr<BasicBlock>) {
        self.set_insertion_point(OpInsertionPoint::AtBlockEnd(block));
    }

    /// Sets the insertion point to after the given operation.
    fn set_insertion_point_after_operation(&mut self, op: Ptr<Operation>) {
        self.set_insertion_point(OpInsertionPoint::AfterOperation(op));
    }

    /// Sets the insertion point to before the given operation.
    fn set_insertion_point_before_operation(&mut self, op: Ptr<Operation>) {
        self.set_insertion_point(OpInsertionPoint::BeforeOperation(op));
    }

    /// Sets the listener for insertion events.
    fn set_listener(&mut self, listener: L);

    /// Gets a reference to the listener for insertion events.
    fn get_listener(&self) -> Option<&L>;

    /// Gets a mutable reference to the listener for insertion events.
    fn get_listener_mut(&mut self) -> Option<&mut L>;
}

/// A utility for inserting [Operation]s from a specified insertion point.
/// Use [DummyListener](super::listener::DummyListener) if no listener is needed.
pub struct IRInserter<L: InsertionListener> {
    op_insertion_point: OpInsertionPoint,
    listener: Option<L>,
}

impl<L: InsertionListener> Default for IRInserter<L> {
    fn default() -> Self {
        Self {
            op_insertion_point: OpInsertionPoint::default(),
            listener: None,
        }
    }
}

impl<L: InsertionListener> IRInserter<L> {
    /// Creates a new [Inserter] that inserts the next operation
    /// at the start of the given [BasicBlock].
    pub fn new_at_block_start(block: Ptr<BasicBlock>) -> Self {
        Self {
            op_insertion_point: OpInsertionPoint::AtBlockStart(block),
            listener: None,
        }
    }

    /// Creates a new [Inserter] that inserts the next operation
    /// at the end of the given [BasicBlock].
    pub fn new_at_block_end(block: Ptr<BasicBlock>) -> Self {
        Self {
            op_insertion_point: OpInsertionPoint::AtBlockEnd(block),
            listener: None,
        }
    }

    /// Creates a new [Inserter] that inserts the next operation
    /// after the given [Operation].
    pub fn new_after_operation(op: Ptr<Operation>) -> Self {
        Self {
            op_insertion_point: OpInsertionPoint::AfterOperation(op),
            listener: None,
        }
    }

    /// Creates a new [Inserter] that inserts the next operation
    /// before the given [Operation].
    pub fn new_before_operation(op: Ptr<Operation>) -> Self {
        Self {
            op_insertion_point: OpInsertionPoint::BeforeOperation(op),
            listener: None,
        }
    }

    /// Creates a new [Inserter] that inserts the next operation
    /// just before the terminator of the given [BasicBlock].
    pub fn new_before_block_terminator(block: Ptr<BasicBlock>, ctx: &Context) -> Self {
        let terminator_op = block
            .deref(ctx)
            .get_terminator(ctx)
            .expect("BasicBlock must have a terminator operation");
        Self::new_before_operation(terminator_op)
    }
}

impl<L: InsertionListener> Inserter<L> for IRInserter<L> {
    fn append_operation(&mut self, ctx: &Context, operation: Ptr<Operation>) {
        // Insert the operation at the current insertion point
        self.insert_operation(ctx, operation);
        // Update the insertion point to be after the newly inserted operation
        self.op_insertion_point = OpInsertionPoint::AfterOperation(operation);
    }

    fn append_op(&mut self, ctx: &Context, op: impl Op) {
        let operation = op.get_operation();
        self.append_operation(ctx, operation);
    }

    fn insert_operation(&mut self, ctx: &Context, operation: Ptr<Operation>) {
        assert!(
            !operation.is_linked(ctx),
            "Cannot insert an already linked operation"
        );
        match self.op_insertion_point {
            OpInsertionPoint::AtBlockStart(block) => {
                // Insert operation at the start of the block
                operation.insert_at_front(block, ctx);
            }
            OpInsertionPoint::AtBlockEnd(block) => {
                // Insert operation at the end of the block
                operation.insert_at_back(block, ctx);
            }
            OpInsertionPoint::AfterOperation(op) => {
                // Insert operation after the specified operation
                operation.insert_after(ctx, op);
            }
            OpInsertionPoint::BeforeOperation(op) => {
                // Insert operation before the specified operation
                operation.insert_before(ctx, op);
            }
            OpInsertionPoint::Unset => {
                panic!("Insertion point is not set");
            }
        }
        // Notify the listener if present
        if let Some(listener) = &mut self.listener {
            listener.notify_operation_inserted(ctx, operation);
        }
    }

    fn insert_op(&mut self, ctx: &Context, op: impl Op) {
        let operation = op.get_operation();
        self.insert_operation(ctx, operation);
    }

    fn insert_block(
        &mut self,
        ctx: &Context,
        insertion_point: BlockInsertionPoint,
        block: Ptr<BasicBlock>,
    ) {
        match insertion_point {
            BlockInsertionPoint::AtRegionStart(region) => {
                block.insert_at_front(region, ctx);
            }
            BlockInsertionPoint::AtRegionEnd(region) => {
                block.insert_at_back(region, ctx);
            }
            BlockInsertionPoint::AfterBlock(prev_block) => {
                block.insert_after(ctx, prev_block);
            }
            BlockInsertionPoint::BeforeBlock(next_block) => {
                block.insert_before(ctx, next_block);
            }
            BlockInsertionPoint::Unset => {
                panic!("Block insertion point is not set");
            }
        }
        // Notify the listener if present
        if let Some(listener) = &mut self.listener {
            listener.notify_block_inserted(ctx, block);
        }
    }

    fn create_block(
        &mut self,
        ctx: &mut Context,
        insertion_point: BlockInsertionPoint,
        label: Option<Identifier>,
        arg_types: Vec<Ptr<TypeObj>>,
    ) -> Ptr<BasicBlock> {
        let block = BasicBlock::new(ctx, label, arg_types);
        self.insert_block(ctx, insertion_point, block);
        self.op_insertion_point = OpInsertionPoint::AtBlockEnd(block);
        block
    }

    fn get_insertion_point(&self) -> OpInsertionPoint {
        self.op_insertion_point
    }

    fn get_insertion_block(&self, ctx: &Context) -> Ptr<BasicBlock> {
        match self.op_insertion_point {
            OpInsertionPoint::AtBlockStart(block) => block,
            OpInsertionPoint::AtBlockEnd(block) => block,
            OpInsertionPoint::AfterOperation(op) => op
                .deref(ctx)
                .get_parent_block()
                .expect("Insertion point Operation must have parent block"),
            OpInsertionPoint::BeforeOperation(op) => op
                .deref(ctx)
                .get_parent_block()
                .expect("Insertion point Operation must have parent block"),
            OpInsertionPoint::Unset => {
                panic!("Insertion point is not set");
            }
        }
    }

    fn set_insertion_point(&mut self, point: OpInsertionPoint) {
        self.op_insertion_point = point;
    }

    /// Sets the listener for insertion events.
    fn set_listener(&mut self, listener: L) {
        self.listener = Some(listener);
    }

    /// Gets a reference to the listener for insertion events.
    fn get_listener(&self) -> Option<&L> {
        self.listener.as_ref()
    }

    /// Gets a mutable reference to the listener for insertion events.
    fn get_listener_mut(&mut self) -> Option<&mut L> {
        self.listener.as_mut()
    }
}
