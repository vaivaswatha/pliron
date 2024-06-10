//! Translate from [inkwell] LLVM-IR to pliron's LLVM dialect

use std::ffi::CStr;

use inkwell::{
    module::Module,
    types::{AnyType, AnyTypeEnum},
    values::{AnyValueEnum, FunctionValue},
};
use pliron::{
    basic_block::BasicBlock,
    builtin::{
        op_interfaces::SingleBlockRegionInterface,
        ops::{FuncOp, ModuleOp},
        types::{FunctionType, IntegerType},
    },
    context::{Context, Ptr},
    input_err_noloc, input_error_noloc,
    op::Op,
    r#type::{TypeObj, TypePtr},
    result::Result,
    use_def_lists::Value,
};
use rustc_hash::FxHashMap;

use crate::types::{ArrayType, PointerType, StructErr, StructType, VoidType};

trait ToStr {
    fn to_str_res(&self) -> Result<&str>;
}

impl ToStr for CStr {
    fn to_str_res(&self) -> Result<&str> {
        self.to_str().map_err(|err| input_error_noloc!(err))
    }
}

pub fn convert_type(ctx: &mut Context, ty: &AnyTypeEnum) -> Result<Ptr<TypeObj>> {
    match ty {
        AnyTypeEnum::ArrayType(aty) => {
            let elem = convert_type(ctx, &aty.get_element_type().as_any_type_enum())?;
            Ok(ArrayType::get(ctx, elem, aty.len() as usize).into())
        }
        AnyTypeEnum::FloatType(_fty) => {
            todo!()
        }
        AnyTypeEnum::FunctionType(fty) => {
            let param_types = fty
                .get_param_types()
                .iter()
                .map(|ty| convert_type(ctx, &ty.as_any_type_enum()))
                .collect::<Result<_>>()?;
            let return_type = fty
                .get_return_type()
                .map(|ty| convert_type(ctx, &ty.as_any_type_enum()))
                .unwrap_or(Ok(VoidType::get(ctx).into()))?;
            // TODO: Use llvm::types::FuncType.
            // Not already doing it because we don't have a corresponding llvm::ops::FuncOp.
            Ok(FunctionType::get(ctx, vec![return_type], param_types).into())
        }
        AnyTypeEnum::IntType(ity) => Ok(IntegerType::get(
            ctx,
            ity.get_bit_width() as u64,
            pliron::builtin::types::Signedness::Signless,
        )
        .into()),
        AnyTypeEnum::PointerType(_pty) => Ok(PointerType::get(ctx).into()),
        AnyTypeEnum::StructType(sty) => {
            if sty.is_opaque() {
                // Opaque structs must be named.
                let Some(name) = sty.get_name() else {
                    return input_err_noloc!(StructErr::OpaqueAndAnonymousErr);
                };
                Ok(StructType::get_named(ctx, name.to_str_res()?, None)?.into())
            } else {
                let field_types: Vec<_> = sty
                    .get_field_types_iter()
                    .map(|ty| convert_type(ctx, &ty.as_any_type_enum()))
                    .collect::<Result<_>>()?;
                if let Some(name) = sty.get_name() {
                    Ok(StructType::get_named(ctx, name.to_str_res()?, Some(field_types))?.into())
                } else {
                    Ok(StructType::get_unnamed(ctx, field_types).into())
                }
            }
        }
        AnyTypeEnum::VectorType(_) => todo!(),
        AnyTypeEnum::VoidType(_) => Ok(VoidType::get(ctx).into()),
    }
}

#[derive(Default)]
struct ConversionContext<'a> {
    // A map from inkwell's Values to pliron's Values.
    _value_map: FxHashMap<AnyValueEnum<'a>, Value>,
    // A map from inkwell's basic blocks to plirons'.
    _block_map: FxHashMap<inkwell::basic_block::BasicBlock<'a>, BasicBlock>,
}

fn convert_function(
    ctx: &mut Context,
    _cctx: &mut ConversionContext,
    function: &FunctionValue,
) -> Result<FuncOp> {
    let name = function.get_name().to_str_res()?;
    let fn_ty = convert_type(ctx, &function.get_type().as_any_type_enum())?;
    let fn_ty = TypePtr::from_ptr(fn_ty, ctx)?;
    let op = FuncOp::new(ctx, name, fn_ty);

    Ok(op)
}

/// Convert [Module] to [ModuleOp].
pub fn convert_module(ctx: &mut Context, module: &Module) -> Result<ModuleOp> {
    let cctx = &mut ConversionContext::default();
    let module_name = module.get_name().to_str_res()?;
    let m = ModuleOp::new(ctx, module_name);
    // TODO: Convert globals.
    // ...
    // Convert functions.
    for fun in module.get_functions() {
        let fun = convert_function(ctx, cctx, &fun)?;
        m.append_operation(ctx, fun.get_operation(), 0);
    }
    Ok(m)
}
