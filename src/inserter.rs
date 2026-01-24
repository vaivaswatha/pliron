//! A utility for inserting [Operation]s from a specified insertion point.
//! Similar in spirit to LLVM's IRBuilder, but does not build operations.

use crate::{
    basic_block::BasicBlock,
    common_traits::Named,
    context::{Context, Ptr},
    identifier::Identifier,
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

impl Printable for OpInsertionPoint {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &printable::State,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        match self {
            OpInsertionPoint::Unset => write!(f, "Insertion Point not set"),
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

/// An interface for insertion of IR entities.
pub trait Inserter: Default {
    /// Appends an [Operation] at the current insertion point.
    /// The insertion point is updated to be after this newly inserted [Operation].
    fn append_operation(&mut self, ctx: &Context, operation: Ptr<Operation>);

    /// Appends an [Op] at the current insertion point.
    /// The insertion point is updated to be after this newly inserted [Op].
    fn append_op(&mut self, ctx: &Context, op: impl Op);

    /// Inserts an [Operation] at the current insertion point.
    /// To insert a sequence in-order, use [append_operation](Self::append_operation).
    fn insert_operation(&self, ctx: &Context, operation: Ptr<Operation>);

    /// Inserts an [Op] at the current insertion point.
    /// To insert a sequence in-order, use [append_op](Self::append_op).
    fn insert_op(&self, ctx: &Context, op: impl Op);

    /// Create a new [BasicBlock] and insert it before the provided marker block.
    /// The insertion point is updated to be at the end of the newly created block.
    fn create_block_before(
        &mut self,
        ctx: &mut Context,
        mark: Ptr<BasicBlock>,
        label: Option<Identifier>,
        arg_types: Vec<Ptr<TypeObj>>,
    );

    /// Create a new [BasicBlock] and insert it after the provided marker block.
    /// The insertion point is updated to be at the end of the newly created block.
    fn create_block_after(
        &mut self,
        ctx: &mut Context,
        mark: Ptr<BasicBlock>,
        label: Option<Identifier>,
        arg_types: Vec<Ptr<TypeObj>>,
    );

    /// Create a new [BasicBlock] and insert it at the start of the provided [Region].
    /// The insertion point is updated to be at the end of the newly created block.
    fn create_block_at_start(
        &mut self,
        ctx: &mut Context,
        region: Ptr<Region>,
        label: Option<Identifier>,
        arg_types: Vec<Ptr<TypeObj>>,
    );

    /// Create a new [BasicBlock] and insert it at the end of the provided [Region].
    /// The insertion point is updated to be at the end of the newly created block.
    fn create_block_at_end(
        &mut self,
        ctx: &mut Context,
        region: Ptr<Region>,
        label: Option<Identifier>,
        arg_types: Vec<Ptr<TypeObj>>,
    );

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
}

/// A utility for inserting [Operation]s from a specified insertion point.
#[derive(Default)]
pub struct IRInserter {
    op_insertion_point: OpInsertionPoint,
}

impl IRInserter {
    /// Creates a new [Inserter] that inserts the next operation
    /// at the start of the given [BasicBlock].
    pub fn new_at_block_start(block: Ptr<BasicBlock>) -> Self {
        Self {
            op_insertion_point: OpInsertionPoint::AtBlockStart(block),
        }
    }

    /// Creates a new [Inserter] that inserts the next operation
    /// at the end of the given [BasicBlock].
    pub fn new_at_block_end(block: Ptr<BasicBlock>) -> Self {
        Self {
            op_insertion_point: OpInsertionPoint::AtBlockEnd(block),
        }
    }

    /// Creates a new [Inserter] that inserts the next operation
    /// after the given [Operation].
    pub fn new_after_operation(op: Ptr<Operation>) -> Self {
        Self {
            op_insertion_point: OpInsertionPoint::AfterOperation(op),
        }
    }

    /// Creates a new [Inserter] that inserts the next operation
    /// before the given [Operation].
    pub fn new_before_operation(op: Ptr<Operation>) -> Self {
        Self {
            op_insertion_point: OpInsertionPoint::BeforeOperation(op),
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

impl Inserter for IRInserter {
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

    fn insert_operation(&self, ctx: &Context, operation: Ptr<Operation>) {
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
    }

    fn insert_op(&self, ctx: &Context, op: impl Op) {
        let operation = op.get_operation();
        self.insert_operation(ctx, operation);
    }

    fn create_block_before(
        &mut self,
        ctx: &mut Context,
        mark: Ptr<BasicBlock>,
        label: Option<Identifier>,
        arg_types: Vec<Ptr<TypeObj>>,
    ) {
        let block = BasicBlock::new(ctx, label, arg_types);
        block.insert_before(ctx, mark);
        self.op_insertion_point = OpInsertionPoint::AtBlockEnd(block);
    }

    fn create_block_after(
        &mut self,
        ctx: &mut Context,
        mark: Ptr<BasicBlock>,
        label: Option<Identifier>,
        arg_types: Vec<Ptr<TypeObj>>,
    ) {
        let block = BasicBlock::new(ctx, label, arg_types);
        block.insert_after(ctx, mark);
        self.op_insertion_point = OpInsertionPoint::AtBlockEnd(block);
    }

    fn create_block_at_start(
        &mut self,
        ctx: &mut Context,
        region: Ptr<Region>,
        label: Option<Identifier>,
        arg_types: Vec<Ptr<TypeObj>>,
    ) {
        let block = BasicBlock::new(ctx, label, arg_types);
        block.insert_at_front(region, ctx);
        self.op_insertion_point = OpInsertionPoint::AtBlockEnd(block);
    }

    fn create_block_at_end(
        &mut self,
        ctx: &mut Context,
        region: Ptr<Region>,
        label: Option<Identifier>,
        arg_types: Vec<Ptr<TypeObj>>,
    ) {
        let block = BasicBlock::new(ctx, label, arg_types);
        block.insert_at_back(region, ctx);
        self.op_insertion_point = OpInsertionPoint::AtBlockEnd(block);
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
}
