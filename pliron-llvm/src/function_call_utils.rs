//! Helper functions to call common simple C functions

use pliron::{
    arg_err,
    builtin::{
        op_interfaces::SymbolTableInterface,
        types::{IntegerType, Signedness},
    },
    context::{Context, Ptr},
    identifier::Identifier,
    result::Result,
    symbol_table::SymbolTableCollection,
    r#type::TypeObj,
};

use crate::{
    ops::FuncOp,
    types::{FuncType, PointerType, VoidType},
};

#[derive(Debug, thiserror::Error)]
pub enum LookupOrInsertFunctionError {
    #[error("Symbol '{0}' found but is not a function")]
    SymbolNotFunction(Identifier),
    #[error("Existing function '{0}' has a different type than the one being inserted")]
    FunctionTypeMismatch(Identifier),
}

/// Looks up a function by name in the given symbol table.
/// If it exists, checks that its type matches the provided type.
/// If it doesn't exist, inserts a new function with the given name and type.
pub fn lookup_or_insert_function(
    ctx: &mut Context,
    symbol_table_collection: &mut SymbolTableCollection,
    symbol_table_op: Box<dyn SymbolTableInterface>,
    name: Identifier,
    return_type: Ptr<TypeObj>,
    param_types: Vec<Ptr<TypeObj>>,
    is_var_arg: bool,
) -> Result<FuncOp> {
    let loc = symbol_table_op.loc(ctx);
    let func_ty = FuncType::get(ctx, return_type, param_types, is_var_arg);
    let symbol_table = symbol_table_collection.get_symbol_table(ctx, symbol_table_op.clone());
    if let Some(func) = symbol_table.lookup(&name) {
        if let Some(func_op) = func.as_any().downcast_ref::<FuncOp>() {
            let existing_func_ty = func_op.get_type(ctx);
            if existing_func_ty != func_ty {
                return arg_err!(loc, LookupOrInsertFunctionError::FunctionTypeMismatch(name));
            }
            Ok(*func_op)
        } else {
            arg_err!(loc, LookupOrInsertFunctionError::SymbolNotFunction(name))
        }
    } else {
        let func = FuncOp::new(ctx, name.clone(), func_ty);
        symbol_table.insert(ctx, Box::new(func), None)?;
        Ok(func)
    }
}

/// Get a declaration to the `malloc` function,
/// inserting it if it doesn't already exist in the symbol table.
pub fn lookup_or_create_malloc_fn(
    ctx: &mut Context,
    symbol_table_collection: &mut SymbolTableCollection,
    symbol_table_op: Box<dyn SymbolTableInterface>,
) -> Result<FuncOp> {
    let size_ty = IntegerType::get(ctx, 64, Signedness::Signless).into();
    lookup_or_insert_function(
        ctx,
        symbol_table_collection,
        symbol_table_op,
        "malloc".try_into().unwrap(),
        PointerType::get(ctx).into(),
        vec![size_ty],
        false,
    )
}

/// Get a declaration to the `free` function,
/// inserting it if it doesn't already exist in the symbol table.
pub fn lookup_or_create_free_fn(
    ctx: &mut Context,
    symbol_table_collection: &mut SymbolTableCollection,
    symbol_table_op: Box<dyn SymbolTableInterface>,
) -> Result<FuncOp> {
    let ptr_ty = PointerType::get(ctx).into();
    lookup_or_insert_function(
        ctx,
        symbol_table_collection,
        symbol_table_op,
        "free".try_into().unwrap(),
        VoidType::get(ctx).into(),
        vec![ptr_ty],
        false,
    )
}

#[cfg(test)]
mod tests {
    use expect_test::expect;
    use pliron::{
        builtin::{
            attributes::IntegerAttr,
            op_interfaces::{
                CallOpCallable, OneResultInterface, SingleBlockRegionInterface, SymbolOpInterface,
            },
            ops::ModuleOp,
            types::{IntegerType, Signedness},
        },
        context::Context,
        op::{Op, verify_op},
        result::ExpectOk,
        utils::apint::APInt,
    };

    use crate::{
        function_call_utils::{lookup_or_create_free_fn, lookup_or_create_malloc_fn},
        llvm_sys::{core::LLVMContext, lljit::LLVMLLJIT, target},
        ops::{CallOp, ConstantOp, FuncOp, ReturnOp},
        to_llvm_ir::convert_module,
        types::{FuncType, VoidType},
    };

    #[test]
    fn test_malloc_and_free_integration() {
        let mut ctx = Context::new();
        let mut symbol_table_collection = pliron::symbol_table::SymbolTableCollection::new();

        // Create a module
        let module = ModuleOp::new(&mut ctx, "test_module".try_into().unwrap());
        let module_box = Box::new(module);

        // Get malloc function
        let malloc_fn =
            lookup_or_create_malloc_fn(&mut ctx, &mut symbol_table_collection, module_box.clone())
                .expect("Failed to create malloc function");

        // Get free function
        let free_fn =
            lookup_or_create_free_fn(&mut ctx, &mut symbol_table_collection, module_box.clone())
                .expect("Failed to create free function");

        // Verify both functions were created
        assert_eq!(
            malloc_fn.get_symbol_name(&ctx),
            "malloc".try_into().unwrap()
        );
        assert_eq!(free_fn.get_symbol_name(&ctx), "free".try_into().unwrap());

        // Verify calling them again returns the same functions
        let malloc_fn_2 =
            lookup_or_create_malloc_fn(&mut ctx, &mut symbol_table_collection, module_box.clone())
                .expect("Failed to get malloc function again");

        assert!(
            malloc_fn == malloc_fn_2,
            "Expected to get the same malloc function on second lookup"
        );

        // Create a main function
        let return_type = VoidType::get(&ctx).into();
        let func_ty = FuncType::get(&mut ctx, return_type, vec![], false);
        let main_fn = FuncOp::new(&mut ctx, "main".try_into().unwrap(), func_ty);
        main_fn
            .get_operation()
            .insert_at_front(module.get_body(&ctx, 0), &ctx);

        let entry = main_fn.get_or_create_entry_block(&mut ctx);
        // Here we would insert calls to malloc and free in the entry block of main
        let size_attr = IntegerAttr::new(
            IntegerType::get(&mut ctx, 64, Signedness::Signless),
            APInt::from_u64(42, 64.try_into().unwrap()),
        );

        let const_op = ConstantOp::new(&mut ctx, size_attr.into());
        const_op.get_operation().insert_at_back(entry, &ctx);

        let size_arg = const_op.get_result(&ctx);
        let callee = CallOpCallable::Direct(malloc_fn.get_symbol_name(&ctx));
        let callee_ty = malloc_fn.get_type(&ctx);
        let args = vec![size_arg];
        let malloc_call = CallOp::new(&mut ctx, callee, callee_ty, args);
        malloc_call.get_operation().insert_at_back(entry, &ctx);

        let ptr_result = malloc_call.get_result(&ctx);
        let free_callee = CallOpCallable::Direct(free_fn.get_symbol_name(&ctx));
        let free_callee_ty = free_fn.get_type(&ctx);
        let free_args = vec![ptr_result];
        let free_call = CallOp::new(&mut ctx, free_callee, free_callee_ty, free_args);
        free_call.get_operation().insert_at_back(entry, &ctx);

        let ret_op = ReturnOp::new(&mut ctx, None);
        ret_op.get_operation().insert_at_back(entry, &ctx);

        verify_op(&module, &ctx).expect_ok(&ctx);

        // Convert to LLVM
        let llvm_ctx = LLVMContext::default();
        let llvm_ir = convert_module(&ctx, &llvm_ctx, module).expect_ok(&ctx);

        expect![[r#"
            ; ModuleID = 'test_module'
            source_filename = "test_module"

            define void @main() {
            entry_block2v1:
              %op6v1_res0 = call ptr @malloc(i64 42)
              call void @free(ptr %op6v1_res0)
              ret void
            }

            declare ptr @malloc(i64)

            declare void @free(ptr)
        "#]]
        .assert_eq(&llvm_ir.to_string());
        llvm_ir.verify().expect("Generated LLVM IR is invalid");

        // Execute the LLVM IR using the JIT and check it runs without errors
        target::initialize_native().expect("Failed to initialize native target for JIT");
        let jit = LLVMLLJIT::new_with_default_builder().expect("Failed to create LLJIT instance");
        jit.add_module(llvm_ir)
            .expect("Failed to add module to JIT");
        let main_addr = jit
            .lookup_symbol("main")
            .expect("Failed to lookup 'main' symbol");
        let main_fn = unsafe { std::mem::transmute::<u64, fn()>(main_addr) };
        main_fn();
    }
}
