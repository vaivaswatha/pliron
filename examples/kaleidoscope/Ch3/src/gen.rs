use std::collections::HashMap;

use pliron::{
    basic_block::BasicBlock,
    context::{Context, Ptr},
    dialects::builtin::{
        op_interfaces::{OneResultInterface, SingleBlockRegionInterface},
        ops::{FuncOp, ModuleOp},
        types::FunctionType,
    },
    op::Op,
    use_def_lists::Value,
};

use crate::{
    ast::{Expr, Program},
    dialect::kal::{self},
    error::{Error, Result},
};

type Args = HashMap<String, Value>;

pub fn generate(ctx: &mut Context, program: Program) -> Result<ModuleOp> {
    let module = ModuleOp::new(ctx, "main");
    let block = module.get_body(ctx, 0);
    let num_ty = kal::NumberType::get(ctx);

    for prototype in program.externs {
        let op = kal::ExternOp::new_unlinked(ctx, prototype.name.as_str(), prototype.args);
        op.get_operation().insert_at_back(block, ctx);
    }

    for function in program.functions {
        let prototype = function.prototype;
        let body = function.body;

        let result_type = vec![num_ty];
        let arg_types = vec![num_ty; prototype.args.len()];
        let fn_type = FunctionType::get(ctx, arg_types, result_type);

        let fn_op = FuncOp::new_unlinked(ctx, prototype.name.as_str(), fn_type);
        fn_op.get_operation().insert_at_back(block, ctx);

        let block = fn_op.get_entry_block(ctx);

        let args: Args = {
            let block_ref = block.deref(ctx);
            prototype
                .args
                .iter()
                .enumerate()
                .map(|(i, arg)| {
                    let arg_op = block_ref.get_argument(i).unwrap();
                    (arg.clone(), arg_op)
                })
                .collect()
        };

        let body = expr(ctx, block, &args, body)?;
        let ret_op = kal::ReturnOp::new_unlinked(ctx, body);
        ret_op.get_operation().insert_at_back(block, ctx);
    }

    if !program.main.is_empty() {
        let main_fn_type = FunctionType::get(ctx, vec![], vec![]);
        let main_fn_op = FuncOp::new_unlinked(ctx, "__main__", main_fn_type);
        main_fn_op.get_operation().insert_at_back(block, ctx);

        let block = main_fn_op.get_entry_block(ctx);
        for e in program.main {
            let _ = expr(ctx, block, &Args::new(), e)?;
        }
    }

    return Ok(module);
}

fn expr(ctx: &mut Context, block: Ptr<BasicBlock>, fn_args: &Args, e: Expr) -> Result<Value> {
    match e {
        Expr::Number(n) => {
            let ty = kal::NumberType::get(ctx);
            let attr = kal::NumberAttr::create(n, ty);
            let op = kal::ConstOp::new_unlinked(ctx, attr);
            op.get_operation().insert_at_back(block, ctx);
            Ok(op.get_result(ctx))
        }
        Expr::Variable(name) => {
            let Some(v) = fn_args.get(name.as_str()) else {
                return Err(Error::VariableNotFound(name));
            };
            Ok(v.clone())
        }
        Expr::Binary { op, lhs, rhs } => {
            let lhs = expr(ctx, block, fn_args, *lhs)?;
            let rhs = expr(ctx, block, fn_args, *rhs)?;
            let op = kal::BinOp::new_unlinked(ctx, convert_op(op), lhs, rhs);
            op.get_operation().insert_at_back(block, ctx);
            Ok(op.get_result(ctx))
        }
        Expr::Call { name, args } => {
            let mut arg_values = vec![];
            for arg in args {
                arg_values.push(expr(ctx, block, fn_args, arg)?);
            }
            let op = kal::CallOp::new_unlinked(ctx, name, arg_values);
            op.get_operation().insert_at_back(block, ctx);
            return Ok(op.get_result(ctx));
        }
    }
}

fn convert_op(op: crate::ast::Operator) -> kal::BinaryOperator {
    match op {
        crate::ast::Operator::LessThan => kal::BinaryOperator::LessThan,
        crate::ast::Operator::Minus => kal::BinaryOperator::Minus,
        crate::ast::Operator::Plus => kal::BinaryOperator::Plus,
        crate::ast::Operator::Times => kal::BinaryOperator::Times,
    }
}