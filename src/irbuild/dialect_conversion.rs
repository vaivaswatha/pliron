//! Utilities for dialect conversion style rewrites.
//! Similar in spirit to MLIR dialect conversion, but intentionally simpler:
//! - no unrealized conversion casts,
//! - definitions are always converted before their uses.

use std::{cell::Ref, collections::VecDeque};

use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    builtin::op_interfaces::IsTerminatorInterface,
    context::{Context, Ptr},
    graph::walkers::{IRNode, WALKCONFIG_PREORDER_FORWARD, uninterruptible::immutable::walk_op},
    irbuild::{
        inserter::{Inserter, OpInsertionPoint},
        listener::{Recorder, RecorderEvent},
        rewriter::{IRRewriter, Rewriter},
    },
    op::op_impls,
    operation::Operation,
    result::Result,
    r#type::{Type, TypeObj, Typed},
    value::Value,
};

/// A rewriter that uses the [Recorder] listener.
pub type DialectConversionRewriter = IRRewriter<Recorder>;

/// Additional type information for operation operands during conversion.
///
/// For each operand, we track a history of previously observed types during conversion.
/// This allows conversion patterns access to evolution of operand types,
/// rather than just the current type. The most recent type before conversion,
/// for each operand, is the last entry.
#[derive(Clone, Default)]
pub struct OperandsInfo(Vec<(Value, Vec<Ptr<TypeObj>>)>);

impl OperandsInfo {
    pub fn new(operands: Vec<(Value, Vec<Ptr<TypeObj>>)>) -> Self {
        Self(operands)
    }

    /// Lookup the most recent (excluding current) `T: Type` recorded for an operand, if any.
    pub fn lookup_most_recent_of_type<'a, T: Type>(
        &self,
        ctx: &'a Context,
        opd: Value,
    ) -> Option<Ref<'a, T>> {
        self.0
            .iter()
            .find(|(operand, _)| *operand == opd)
            .and_then(|(_, previous_types)| {
                previous_types.iter().rev().find_map(|ty| {
                    let ty_ref = ty.deref(ctx);
                    Ref::filter_map(ty_ref, |ty_ref| ty_ref.downcast_ref::<T>()).ok()
                })
            })
    }

    /// Lookup the most recent type (excluding current) recorded for an operand, if any.
    pub fn lookup_most_recent_type(&self, opd: Value) -> Option<Ptr<TypeObj>> {
        self.0
            .iter()
            .find(|(operand, _)| *operand == opd)
            .and_then(|(_, previous_types)| previous_types.last().cloned())
    }

    /// Lookup the full history of types (excluding current) recorded for an operand,
    /// ordered from oldest to newest.
    pub fn lookup_operand_history(&self, opd: Value) -> Vec<Ptr<TypeObj>> {
        self.0
            .iter()
            .find(|(operand, _)| *operand == opd)
            .map(|(_, previous_types)| previous_types.clone())
            .unwrap_or_default()
    }
}

/// Interface for dialect conversion matching and rewriting.
pub trait DialectConversion {
    /// Should this operation be converted?
    fn can_convert_op(&mut self, ctx: &Context, op: Ptr<Operation>) -> bool;

    /// Should this type be converted?
    fn can_convert_type(&mut self, _ctx: &Context, _ty: Ptr<TypeObj>) -> bool {
        false
    }

    /// Convert the type and return the converted type.
    fn convert_type(&mut self, _ctx: &mut Context, ty: Ptr<TypeObj>) -> Result<Ptr<TypeObj>> {
        Ok(ty)
    }

    /// Rewrite the operation.
    ///
    /// Insertion point is set to be before the operation being rewritten.
    /// All operands are already converted before this callback is invoked.
    /// `operands_info` provides the current operand values along with their
    /// historical types observed during conversion. The last type in the history
    /// is the most recent type before conversion.
    fn rewrite(
        &mut self,
        ctx: &mut Context,
        rewriter: &mut DialectConversionRewriter,
        op: Ptr<Operation>,
        operands_info: &OperandsInfo,
    ) -> Result<()>;
}

/// Applies dialect conversion rewrites rooted at `op`.
///
/// Conversion is trait-driven and recursively ensures that any convertible
/// operand definitions are rewritten before rewriting the current operation.
///
/// Block argument types are updated only in two cases:
/// 1. The block argument is an operand use of an operation being processed.
/// 2. An operation being processed has successor blocks, in which case all
///    arguments of those successor blocks are considered for type conversion.
pub fn apply_dialect_conversion<C: DialectConversion>(
    ctx: &mut Context,
    conversion: &mut C,
    op: Ptr<Operation>,
) -> Result<()> {
    struct Driver<'a, C: DialectConversion> {
        ctx: &'a mut Context,
        conversion: &'a mut C,
        rewriter: DialectConversionRewriter,
        erased_ops: FxHashSet<Ptr<Operation>>,
        in_progress: FxHashSet<Ptr<Operation>>,
        previous_types: FxHashMap<Value, Vec<Ptr<TypeObj>>>,
    }

    impl<'a, C: DialectConversion> Driver<'a, C> {
        fn new(ctx: &'a mut Context, conversion: &'a mut C) -> Self {
            let mut rewriter = DialectConversionRewriter::default();
            rewriter.set_listener(Recorder::default());
            Self {
                ctx,
                conversion,
                rewriter,
                erased_ops: FxHashSet::default(),
                in_progress: FxHashSet::default(),
                previous_types: FxHashMap::default(),
            }
        }

        fn collect_operations(&mut self, root: Ptr<Operation>) -> VecDeque<Ptr<Operation>> {
            let mut ops = VecDeque::new();
            fn walker_callback<C: DialectConversion>(
                ctx: &Context,
                state: &mut Driver<'_, C>,
                node: IRNode,
            ) {
                if let IRNode::Operation(op) = node {
                    let is_terminator = {
                        let op_obj = Operation::get_op_dyn(op, ctx);
                        op_impls::<dyn IsTerminatorInterface>(op_obj.as_ref())
                    };
                    if state.conversion.can_convert_op(ctx, op) || is_terminator {
                        state.worklist.push_back(op);
                    }
                }
            }
            struct Driver<'a, C: DialectConversion> {
                conversion: &'a mut C,
                worklist: &'a mut VecDeque<Ptr<Operation>>,
            }
            let mut state = Driver {
                conversion: self.conversion,
                worklist: &mut ops,
            };
            walk_op(
                self.ctx,
                &mut state,
                &WALKCONFIG_PREORDER_FORWARD,
                root,
                walker_callback::<C>,
            );
            ops
        }

        fn append_type_history(
            existing: &mut Vec<Ptr<TypeObj>>,
            mut additional: Vec<Ptr<TypeObj>>,
        ) {
            for ty in additional.drain(..) {
                if !existing.contains(&ty) {
                    existing.push(ty);
                }
            }
        }

        fn record_replacement(
            &mut self,
            old_values: Vec<Value>,
            old_types: Vec<Ptr<TypeObj>>,
            new_values: Vec<Value>,
        ) {
            for ((old_value, old_type), new_value) in old_values
                .into_iter()
                .zip(old_types.into_iter())
                .zip(new_values.into_iter())
            {
                let mut history = self.previous_types.remove(&old_value).unwrap_or_default();
                history.push(old_type);
                let existing = self.previous_types.entry(new_value).or_default();
                Self::append_type_history(existing, history);
            }
        }

        fn record_type_change(&mut self, value: Value, old_type: Ptr<TypeObj>) {
            let existing = self.previous_types.entry(value).or_default();
            Self::append_type_history(existing, vec![old_type]);
        }

        fn convert_block_argument_type(&mut self, value: Value) -> Result<()> {
            assert!(matches!(value, Value::BlockArgument { .. }));

            loop {
                let current_type = value.get_type(self.ctx);
                if !self.conversion.can_convert_type(self.ctx, current_type) {
                    break;
                }

                let converted_type = self.conversion.convert_type(self.ctx, current_type)?;
                if converted_type == current_type {
                    break;
                }

                self.rewriter
                    .set_value_type(self.ctx, value, converted_type);
                self.process_recorder_events()?;
            }

            Ok(())
        }

        fn convert_successor_block_argument_types(&mut self, op: Ptr<Operation>) -> Result<()> {
            let successors: Vec<_> = op.deref(self.ctx).successors().collect();
            for succ in successors {
                let args: Vec<_> = succ.deref(self.ctx).arguments().collect();
                for arg in args {
                    self.convert_block_argument_type(arg)?;
                }
            }
            Ok(())
        }

        fn process_recorder_events(&mut self) -> Result<()> {
            let events = {
                let listener = self
                    .rewriter
                    .get_listener_mut()
                    .expect("Rewriter must have a listener attached");
                std::mem::take(&mut listener.events)
            };

            for event in &events {
                if let RecorderEvent::ErasedOperation(op) = event {
                    self.erased_ops.insert(*op);
                }
            }

            for event in &events {
                match event {
                    RecorderEvent::ReplacedOperation {
                        old_values,
                        old_types,
                        new_values,
                    } => {
                        self.record_replacement(
                            old_values.clone(),
                            old_types.clone(),
                            new_values.clone(),
                        );
                    }
                    RecorderEvent::ValueTypeChanged {
                        value,
                        old_type,
                        new_type: _,
                    } => {
                        self.record_type_change(*value, *old_type);
                    }
                    RecorderEvent::InsertedOperation(_) => {}
                    RecorderEvent::ErasedOperation(_)
                    | RecorderEvent::InsertedBlock(_)
                    | RecorderEvent::ErasedBlock(_)
                    | RecorderEvent::ErasedRegion(_)
                    | RecorderEvent::UnlinkedOperation(_, _)
                    | RecorderEvent::UnlinkedBlock(_, _) => {}
                }
            }

            for event in events {
                if let RecorderEvent::InsertedOperation(new_op) = event
                    && !self.erased_ops.contains(&new_op)
                    && (self.conversion.can_convert_op(self.ctx, new_op)
                        || op_impls::<dyn IsTerminatorInterface>(&*Operation::get_op_dyn(
                            new_op, self.ctx,
                        )))
                {
                    self.convert_operation(new_op)?;
                }
            }

            Ok(())
        }

        fn convert_operation(&mut self, op: Ptr<Operation>) -> Result<()> {
            if self.erased_ops.contains(&op) || self.in_progress.contains(&op) {
                return Ok(());
            }

            self.convert_successor_block_argument_types(op)?;

            if !self.conversion.can_convert_op(self.ctx, op) {
                return Ok(());
            }

            self.in_progress.insert(op);

            let operands: Vec<_> = op.deref(self.ctx).operands().collect();
            for operand in &operands {
                match operand {
                    Value::OpResult { op: def_op, .. } => {
                        if *def_op == op || self.erased_ops.contains(def_op) {
                            continue;
                        }
                        self.convert_operation(*def_op)?;
                    }
                    Value::BlockArgument { .. } => self.convert_block_argument_type(*operand)?,
                }
            }

            if self.erased_ops.contains(&op) {
                self.in_progress.remove(&op);
                return Ok(());
            }

            if !self.conversion.can_convert_op(self.ctx, op) {
                self.in_progress.remove(&op);
                return Ok(());
            }

            let operands_info = OperandsInfo::new(
                operands
                    .into_iter()
                    .map(|operand| {
                        (
                            operand,
                            self.previous_types
                                .get(&operand)
                                .cloned()
                                .unwrap_or_default(),
                        )
                    })
                    .collect(),
            );

            self.rewriter
                .set_insertion_point(OpInsertionPoint::BeforeOperation(op));
            self.conversion
                .rewrite(self.ctx, &mut self.rewriter, op, &operands_info)?;
            self.process_recorder_events()?;

            self.in_progress.remove(&op);
            Ok(())
        }

        fn run(&mut self, root: Ptr<Operation>) -> Result<()> {
            let mut worklist = self.collect_operations(root);
            while let Some(op) = worklist.pop_front() {
                self.convert_operation(op)?;
            }
            Ok(())
        }
    }

    let mut driver = Driver::new(ctx, conversion);
    driver.run(op)
}
