use crate::context::Context;
use crate::context::Ptr;
use crate::error::CompilerError;
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
    pub fn run(&mut self, ctx: &mut Context, op: Ptr<Operation>) -> Result<(), CompilerError> {
        for pass in self.passes.iter_mut() {
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

    fn run_on_operation(&self, ctx: &mut Context, op: Ptr<Operation>) -> Result<(), CompilerError>;
}
