use apint::ApInt;
use expect_test::expect;
use pliron::common_traits::Verify;
use pliron::context::Context;
use pliron::context::Ptr;
use pliron::debug_info::set_operation_result_name;
use pliron::dialect::Dialect;
use pliron::dialect::DialectName;
use pliron::dialect_conversion::apply_partial_conversion;
use pliron::dialect_conversion::ConversionTarget;
use pliron::dialects;
use pliron::dialects::builtin::attributes::IntegerAttr;
use pliron::dialects::builtin::op_interfaces::OneResultInterface;
use pliron::dialects::builtin::ops::ConstantOp;
use pliron::dialects::builtin::ops::FuncOp;
use pliron::dialects::builtin::ops::ModuleOp;
use pliron::dialects::builtin::types::FunctionType;
use pliron::dialects::builtin::types::IntegerType;
use pliron::dialects::builtin::types::Signedness;
use pliron::dialects::llvm::ops::ReturnOp;
use pliron::error::CompilerError;
use pliron::op::Op;
use pliron::operation::Operation;
use pliron::pass::Pass;
use pliron::pass::PassManager;
use pliron::pattern_match::MatchResult;
use pliron::pattern_match::PatternRewriter;
use pliron::pattern_match::RewritePattern;
use pliron::rewrite::RewritePatternSet;
use pliron::with_context::AttachContext;

// since there is not much ops in llvm dialect so far, let's swap all the constants with constant of 1
#[derive(Debug, Default)]
pub struct TestLoweringRewritePattern {}

impl RewritePattern for TestLoweringRewritePattern {
    fn match_op(&self, ctx: &Context, op: Ptr<Operation>) -> MatchResult {
        if op
            .deref(ctx)
            .get_op(ctx)
            .downcast_ref::<ConstantOp>()
            .is_some()
        {
            MatchResult::Success
        } else {
            MatchResult::Fail
        }
    }

    fn rewrite(
        &self,
        ctx: &mut Context,
        op: Ptr<Operation>,
        rewriter: &mut dyn PatternRewriter,
    ) -> Result<(), CompilerError> {
        let i64_ty = IntegerType::get(ctx, 64, Signedness::Signed);
        let one_const = IntegerAttr::create(i64_ty, ApInt::from(1));
        let new_op = ConstantOp::new_unlinked(ctx, one_const);
        rewriter.replace_op_with(ctx, op, new_op.get_operation())?;
        Ok(())
    }
}

pub struct TestLoweringPass {}

impl Pass for TestLoweringPass {
    fn name(&self) -> &str {
        "test-pass"
    }

    fn run_on_operation(
        &mut self,
        ctx: &mut Context,
        op: Ptr<Operation>,
    ) -> Result<(), CompilerError> {
        let mut target = ConversionTarget::new();
        target.add_illegal_dialect(Dialect::get_ref(ctx, DialectName::new("builtin")).unwrap());
        target.add_legal_dialect(Dialect::get_ref(ctx, DialectName::new("llvm")).unwrap());
        let mut patterns = RewritePatternSet::default();
        patterns.add(Box::<TestLoweringRewritePattern>::default());
        apply_partial_conversion(ctx, op, &target, patterns)?;
        Ok(())
    }
}

fn setup_context_dialects() -> Context {
    let mut ctx = Context::new();
    dialects::builtin::register(&mut ctx);
    dialects::llvm::register(&mut ctx);
    ctx
}

// Create a print a module "bar", with a function "foo"
// containing a single `return 0`.
fn create_mod_op(
    ctx: &mut Context,
) -> Result<(ModuleOp, FuncOp, ConstantOp, ReturnOp), CompilerError> {
    let i64_ty = IntegerType::get(ctx, 64, Signedness::Signed);
    let module = ModuleOp::new(ctx, "bar");
    // Our function is going to have type () -> ().
    let func_ty = FunctionType::get(ctx, vec![], vec![i64_ty]);
    let func = FuncOp::new_unlinked(ctx, "foo", func_ty);
    module.add_operation(ctx, func.get_operation());
    let bb = func.get_entry_block(ctx);

    // Create a `const 0` op and add it to bb.
    let zero_const = IntegerAttr::create(i64_ty, ApInt::from(0));
    let const_op = ConstantOp::new_unlinked(ctx, zero_const);
    const_op.get_operation().insert_at_front(bb, ctx);
    set_operation_result_name(ctx, const_op.get_operation(), 0, "c0".to_string());

    // Return the constant.
    let ret_op = ReturnOp::new_unlinked(ctx, const_op.get_result(ctx));
    ret_op.get_operation().insert_at_back(bb, ctx);

    println!("{}", module.with_ctx(ctx));
    module.verify(ctx)?;

    Ok((module, func, const_op, ret_op))
}

#[test]
fn run_pass() {
    // since there is not much ops in llvm dialect so far, let's swap all the constants with constant of 1
    let mut ctx = setup_context_dialects();
    let (module, _, _, _) = create_mod_op(&mut ctx).unwrap();
    // before the transformation
    expect![[r#"
        builtin.module @bar {
          block_0_0():
            builtin.func @foo() -> (si64,) {
              entry():
                c0 = builtin.constant 0x0: si64
                llvm.return c0
            }
        }"#]]
    .assert_eq(&module.with_ctx(&ctx).to_string());
    let mut pm = PassManager::new();
    pm.add_pass(Box::new(TestLoweringPass {}));
    pm.run(&mut ctx, module.get_operation()).unwrap();
    // after the transformation
    expect![[r#"
        builtin.module @bar {
          block_0_0():
            builtin.func @foo() -> (si64,) {
              entry():
                c0 = builtin.constant 0x1: si64
                llvm.return c0
            }
        }"#]]
    .assert_eq(&module.with_ctx(&ctx).to_string());
}
