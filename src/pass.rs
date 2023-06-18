use crate::context::Context;
use crate::context::Ptr;
use crate::dialect_conversion::ConversionError;
use crate::operation::Operation;

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
            pass.run_on_operation(ctx, op)?;
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

    fn run_on_operation(&self, ctx: &mut Context, op: Ptr<Operation>) -> Result<(), PassError>;
}

#[derive(thiserror::Error, Debug)]
pub enum PassError {
    #[error("Conversion failed: {0}")]
    ConversionError(#[from] ConversionError),
}
