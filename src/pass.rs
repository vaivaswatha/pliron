use crate::context::Context;
use crate::context::Ptr;
use crate::operation::Operation;
use crate::with_context::AttachContext;

#[derive(Default)]
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

    /// Run all of the passes on the given operation.
    pub fn run(&self, ctx: &mut Context, op: Ptr<Operation>) -> Result<(), PassError> {
        for pass in self.passes.iter() {
            pass.run_on_operation(ctx, op)
                .map_err(|e| PassError::Failure {
                    cause: e.into(),
                    pass: pass.name().to_string(),
                    root_op: op.with_ctx(ctx).to_string(),
                })?;
        }
        Ok(())
    }
}

/// Pass to transform an operation of a specific type.
/// Operation passes must not:
///   - modify any other operations within the parent region, as other threads
///     may be manipulating them concurrently.
///   - modify any state within the parent operation, this includes adding
///     additional operations.
pub trait Pass {
    fn name(&self) -> &str;

    fn run_on_operation(&self, ctx: &mut Context, op: Ptr<Operation>) -> Result<(), anyhow::Error>;
}

#[derive(thiserror::Error, Debug)]
pub enum PassError {
    #[error("Pass failed: {cause} in pass {pass} on op {root_op}")]
    Failure {
        cause: anyhow::Error,
        pass: String,
        root_op: String,
    },
}
