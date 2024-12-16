use pliron::{
    builtin,
    context::Context,
    dialect::{Dialect, DialectName},
};

pub fn setup_context_dialects() -> Context {
    let mut ctx = Context::new();
    builtin::register(&mut ctx);
    // Create a test dialect for test ops/attributes and types.
    let test_dialect = Dialect::new(DialectName::new("test"));
    test_dialect.register(&mut ctx);
    ctx
}
