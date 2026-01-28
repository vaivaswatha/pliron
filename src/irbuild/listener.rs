//! Listen to IR building / rewriting events.

use crate::{
    basic_block::BasicBlock,
    context::{Context, Ptr},
    operation::Operation,
};

/// Listener interface for insertion events.
pub trait InsertionListener {
    /// Notify that an operation has been inserted.
    fn notify_operation_inserted(&mut self, ctx: &Context, operation: Ptr<Operation>);
    /// Notify that a block has been created.
    fn notify_block_created(&mut self, ctx: &Context, block: Ptr<BasicBlock>);
}

/// Listener interface for rewrite events.
pub trait RewriteListener: InsertionListener {
    /// Notify that an operation is about to be erased.
    fn notify_operation_erasure(&mut self, ctx: &Context, op: Ptr<Operation>);
    /// Notify that an operation is about to be replaced.
    fn notify_operation_replacement(
        &mut self,
        ctx: &Context,
        old_op: Ptr<Operation>,
        new_op: Ptr<Operation>,
    );
}

/// A listerner that doesn't do anything on being notified.
pub struct DummyListener;
impl InsertionListener for DummyListener {
    fn notify_operation_inserted(&mut self, _ctx: &Context, _operation: Ptr<Operation>) {}
    fn notify_block_created(&mut self, _ctx: &Context, _block: Ptr<BasicBlock>) {}
}
impl RewriteListener for DummyListener {
    fn notify_operation_erasure(&mut self, _ctx: &Context, _op: Ptr<Operation>) {}
    fn notify_operation_replacement(
        &mut self,
        _ctx: &Context,
        _old_op: Ptr<Operation>,
        _new_op: Ptr<Operation>,
    ) {
    }
}

/// Events recorded by the [Recorder] listener.
pub enum RecorderEvent {
    InsertedOperation(Ptr<Operation>),
    CreatedBlock(Ptr<BasicBlock>),
    ErasedOperation(Ptr<Operation>),
    ReplacedOperation(Ptr<Operation>, Ptr<Operation>),
}

/// A listener that records events in the order they occur.
#[derive(Default)]
pub struct Recorder {
    pub events: Vec<RecorderEvent>,
}

impl InsertionListener for Recorder {
    fn notify_operation_inserted(&mut self, _ctx: &Context, operation: Ptr<Operation>) {
        self.events
            .push(RecorderEvent::InsertedOperation(operation));
    }

    fn notify_block_created(&mut self, _ctx: &Context, block: Ptr<BasicBlock>) {
        self.events.push(RecorderEvent::CreatedBlock(block));
    }
}

impl RewriteListener for Recorder {
    fn notify_operation_erasure(&mut self, _ctx: &Context, op: Ptr<Operation>) {
        self.events.push(RecorderEvent::ErasedOperation(op));
    }

    fn notify_operation_replacement(
        &mut self,
        _ctx: &Context,
        old_op: Ptr<Operation>,
        new_op: Ptr<Operation>,
    ) {
        self.events
            .push(RecorderEvent::ReplacedOperation(old_op, new_op));
    }
}

impl Recorder {
    /// Clear all recorded events.
    pub fn clear(&mut self) {
        self.events.clear();
    }
}
