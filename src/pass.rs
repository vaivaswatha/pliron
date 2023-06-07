use rustc_hash::FxHashMap;

use crate::context::Context;
use crate::context::Ptr;
use crate::dialect::Dialect;
use crate::dialect::DialectName;
use crate::error::CompilerError;
use crate::op::Op;
use crate::op::OpId;
use crate::operation::Operation;

pub struct PassManager {
    passes: Vec<Box<dyn Pass>>,
}

impl PassManager {
    pub fn new() -> Self {
        Self { passes: vec![] }
    }

    pub fn add_pass(&mut self, pass: Box<dyn Pass>) {
        self.passes.push(pass);
    }

    pub fn run(&mut self, ctx: &mut Context, op: Ptr<Operation>) -> Result<(), CompilerError> {
        for pass in self.passes.iter_mut() {
            pass.run_on_operation(ctx, op)?;
        }
        Ok(())
    }
}

impl Default for PassManager {
    fn default() -> Self {
        Self::new()
    }
}

/// from MLIR's OpeationPass:
/// Pass to transform an operation of a specific type.
///
/// Operation passes must not:
///   - modify any other operations within the parent region, as other threads
///     may be manipulating them concurrently.
///   - modify any state within the parent operation, this includes adding
///     additional operations.
pub trait Pass {
    fn name(&self) -> &str;

    fn run_on_operation(
        &mut self,
        ctx: &mut Context,
        op: Ptr<Operation>,
    ) -> Result<(), CompilerError>;
}

/// This enumeration corresponds to the specific action to take when
/// considering an operation legal for this conversion target.
pub enum LegalizationAction {
    /// The target supports this operation.
    Legal,

    /// This operation has dynamic legalization constraints that must be checked
    /// by the target.
    Dynamic,

    /// The target explicitly does not support this operation.
    Illegal,
}

pub struct ConversionTarget {
    legal_dialects: FxHashMap<DialectName, LegalizationAction>,
}

impl ConversionTarget {
    pub fn new() -> Self {
        Self {
            legal_dialects: FxHashMap::default(),
        }
    }

    pub fn add_legal_dialect(&mut self, dialect: &Dialect) {
        self.legal_dialects
            .entry(dialect.get_name().clone())
            .or_insert(LegalizationAction::Legal);
    }
    pub fn add_illegal_dialect(&mut self, dialect: &Dialect) {
        self.legal_dialects
            .entry(dialect.get_name().clone())
            .or_insert(LegalizationAction::Illegal);
    }
    pub fn add_dynamically_legal_op<OpT: Op>(&mut self, _callback: fn(Ptr<Operation>) -> bool) {
        self.set_op_action(OpT::get_opid_static(), LegalizationAction::Dynamic);
        todo!("set legality callback");
    }
    fn set_op_action(&mut self, _op_id: OpId, _action: LegalizationAction) {
        todo!()
    }
}

impl Default for ConversionTarget {
    fn default() -> Self {
        Self::new()
    }
}
