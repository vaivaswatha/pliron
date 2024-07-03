//! Translate from pliron's LLVM dialec to [inkwell]

use apint::ApInt;
use pliron::{
    basic_block::BasicBlock,
    builtin::{
        attributes::{FloatAttr, IntegerAttr},
        op_interfaces::{
            BranchOpInterface, OneOpdInterface, OneRegionInterface, OneResultInterface,
            SingleBlockRegionInterface, SymbolOpInterface,
        },
        ops::{FuncOp, ModuleOp},
        types::{FunctionType, IntegerType},
    },
    common_traits::Named,
    context::{Context, Ptr},
    decl_op_interface, decl_type_interface, impl_op_interface, impl_type_interface, input_err,
    input_err_noloc, input_error, input_error_noloc,
    linked_list::{ContainsLinkedList, LinkedList},
    location::Located,
    op::{op_cast, Op},
    operation::Operation,
    r#type::{type_cast, Type, TypeObj, TypePtr, Typed},
    result::Result,
    use_def_lists::Value,
    utils::traversals::region::topological_order,
};

use inkwell::{
    basic_block::BasicBlock as IWBasicBlock,
    builder::Builder,
    context::Context as IWContext,
    module::Module as IWModule,
    types::{
        self as iwtypes, AnyType, AnyTypeEnum, BasicMetadataTypeEnum, BasicType, BasicTypeEnum,
        IntType,
    },
    values::{
        AnyValue, AnyValueEnum, BasicValueEnum, FunctionValue, IntValue, PhiValue, PointerValue,
    },
    IntPredicate,
};

use rustc_hash::FxHashMap;
use thiserror::Error;

use crate::{
    attributes::ICmpPredicateAttr,
    op_interfaces::PointerTypeResult,
    ops::{
        AddOp, AllocaOp, AndOp, BitcastOp, BrOp, CondBrOp, ConstantOp, ICmpOp, LoadOp, MulOp, OrOp,
        ReturnOp, SDivOp, SRemOp, ShlOp, StoreOp, SubOp, UDivOp, URemOp, UndefOp, XorOp,
    },
    types::{ArrayType, PointerType, StructType, VoidType},
};

/// Mapping from pliron entities to inkwell entities.
pub struct ConversionContext<'ctx> {
    // A map from inkwell's Values to pliron's Values.
    value_map: FxHashMap<Value, AnyValueEnum<'ctx>>,
    // A map from inkwell's basic blocks to plirons'.
    block_map: FxHashMap<Ptr<BasicBlock>, IWBasicBlock<'ctx>>,
    // The active LLVM / inkwell [Builder].
    builder: Builder<'ctx>,
}

impl<'ctx> ConversionContext<'ctx> {
    pub fn new(iwctx: &'ctx IWContext) -> Self {
        Self {
            value_map: FxHashMap::default(),
            block_map: FxHashMap::default(),
            builder: iwctx.create_builder(),
        }
    }
}

#[derive(Error, Debug)]
pub enum ToLLVMErr {
    #[error("Type {0} does not have a conversion to LLVM type implemented")]
    MissingTypeConversion(String),
    #[error("Operation {0} does not have a conversion to LLVM instruction implemented")]
    MissingOpConversion(String),
    #[error("Array element type must be a basic type")]
    ArrayElementTypeNotBasic,
    #[error("Function type's return type and argument types must all be a basic type")]
    FunctionTypeComponentNotBasic,
    #[error("Struct field type must be a basic type")]
    StructFieldTypeNotBasic,
    #[error("FuncOp must implement ToLLVMType and have FunctionType")]
    FuncOpTypeErr,
    #[error("PHI argument must be a basic type")]
    PhiTypeNotBasic,
    #[error("Definition for value {0} not seen yet")]
    UndefinedValue(String),
    #[error("Block definition {0} not seen yet")]
    UndefinedBlock(String),
    #[error("Integer instruction must have integer operands")]
    IntOpValueErr,
    #[error("AllocaOp pointee type must be basic type")]
    AllocaOpTypeNotBasic,
    #[error("AllocaOp size operand must be IntType")]
    AllocaOpSizeNotInt,
    #[error("BitcastOp operand must be basic")]
    BitcastOpOpdNotBasic,
    #[error("BitcastOp result must be a basic type")]
    BitcastOpResultNotBasicType,
    #[error("Number of block args in the source dialect equal the number of PHIs in target IR")]
    NumBlockArgsNumPhisMismatch,
    #[error("Value passed to block argument must be BasicValue")]
    BranchArgNotBasic,
    #[error("Conditional branch's condition must be an IntValue")]
    CondBranchCondNotInt,
    #[error("Load operand must be a PointerVal")]
    LoadOpdNotPointer,
    #[error("Loaded value must have BasicType")]
    LoadedValueNotBasicType,
    #[error("Stored value must have BasicType")]
    StoredValueNotBasicType,
    #[error("Store pointer must be PointerVal")]
    StorePointerIncorrect,
    #[error("ConstantOp must have integer or float value")]
    ConstOpNotIntOrFloat,
    #[error("ICmpOp operands must be IntValues")]
    ICmpOpOpdNotInt,
    #[error("ReturnOp must return a BasicType")]
    ReturnOpOperandNotBasic,
}

pub fn convert_ipredicate(pred: ICmpPredicateAttr) -> IntPredicate {
    match pred {
        ICmpPredicateAttr::EQ => IntPredicate::EQ,
        ICmpPredicateAttr::NE => IntPredicate::NE,
        ICmpPredicateAttr::UGT => IntPredicate::UGT,
        ICmpPredicateAttr::UGE => IntPredicate::UGE,
        ICmpPredicateAttr::ULT => IntPredicate::ULT,
        ICmpPredicateAttr::ULE => IntPredicate::ULE,
        ICmpPredicateAttr::SGT => IntPredicate::SGT,
        ICmpPredicateAttr::SGE => IntPredicate::SGE,
        ICmpPredicateAttr::SLT => IntPredicate::SLT,
        ICmpPredicateAttr::SLE => IntPredicate::SLE,
    }
}

decl_type_interface! {
    /// A type that implements this is convertible to an inkwell [AnyTypeEnum].
    ToLLVMType {
        /// Convert from pliron [Type] to inkwell's [AnyTypeEnum].
        fn convert<'ctx>(
            &self,
            ctx: &Context,
            iwctx: &'ctx IWContext) -> Result<AnyTypeEnum<'ctx>>;

        fn verify(_type: &dyn Type, _ctx: &Context) -> Result<()>
        where Self: Sized,
        {
            Ok(())
        }
    }
}

decl_op_interface! {
    /// An [Op] that implements this is convertible to an inkwell [AnyValueEnum].
    ToLLVMValue {
        /// Convert from pliron [Op] to inkwell's [AnyValueEnum].
        fn convert<'ctx>(
            &self, ctx: &Context,
            iwctx: &'ctx IWContext,
            cctx: &mut ConversionContext<'ctx>) -> Result<AnyValueEnum<'ctx>>;

        fn verify(_op: &dyn Op, _ctx: &Context) -> Result<()>
        where Self: Sized,
        {
            Ok(())
        }
    }
}

impl_type_interface!(
    ToLLVMType for IntegerType {
        fn convert<'ctx>(
            &self,
            _ctx: &Context,
            iwctx: &'ctx IWContext) -> Result<AnyTypeEnum<'ctx>>
        {
            Ok(AnyTypeEnum::IntType(iwctx.custom_width_int_type(self.get_width())))
        }
    }
);

impl_type_interface!(
    ToLLVMType for ArrayType {
        fn convert<'ctx>(
            &self,
            ctx: &Context,
            iwctx: &'ctx IWContext) -> Result<AnyTypeEnum<'ctx>>
        {
            let el_ty = convert_type(ctx, iwctx, self.elem_type())?;
            let el_ty_basic: BasicTypeEnum =
                TryFrom::try_from(el_ty)
                .map_err(|_err| input_error_noloc!(ToLLVMErr::ArrayElementTypeNotBasic))?;
            Ok(el_ty_basic.array_type(
                self.size().try_into()
                .expect("LLVM's ArrayType's size is u64, \
                        but inkwell uses u32 and we can't fit it in u32"))
                .as_any_type_enum()
            )
        }
    }
);

impl_type_interface!(
    ToLLVMType for FunctionType {
        fn convert<'ctx>(
            &self,
            ctx: &Context,
            iwctx: &'ctx IWContext) -> Result<AnyTypeEnum<'ctx>>
        {
            let args_tys: Vec<_> =
                self.get_inputs()
                .iter()
                .map(|ty| {
                    let ty: BasicTypeEnum =
                        convert_type(ctx, iwctx, *ty)?
                        .try_into()
                        .map_err(|_err| {
                            input_error_noloc!(ToLLVMErr::FunctionTypeComponentNotBasic)
                        })?;
                    Ok(BasicMetadataTypeEnum::from(ty))
                })
                .collect::<Result<_>>()?;
            let ret_ty: BasicTypeEnum =
                self.get_results().first().map(|ty| convert_type(ctx, iwctx, *ty))
                .unwrap_or(Ok(iwctx.void_type().as_any_type_enum()))?
                .try_into()
                .map_err(|_err| input_error_noloc!(ToLLVMErr::FunctionTypeComponentNotBasic))?;
            Ok(ret_ty.fn_type(&args_tys, false).as_any_type_enum())
        }
    }
);

impl_type_interface!(
    ToLLVMType for VoidType {
        fn convert<'ctx>(
            &self,
            _ctx: &Context,
            iwctx: &'ctx IWContext) -> Result<AnyTypeEnum<'ctx>>
        {
            Ok(iwctx.void_type().as_any_type_enum())
        }
    }
);

impl_type_interface!(
    ToLLVMType for PointerType {
        fn convert<'ctx>(
            &self,
            _ctx: &Context,
            _iwctx: &'ctx IWContext) -> Result<AnyTypeEnum<'ctx>>
        {
            // Ok(iwctx.ptr_type(0).as_any_type_enum())
            todo!()
        }
    }
);

impl_type_interface!(
    ToLLVMType for StructType {
        fn convert<'ctx>(
            &self,
            ctx: &Context,
            iwctx: &'ctx IWContext) -> Result<AnyTypeEnum<'ctx>>
        {
            if self.is_opaque() {
                let name = self.name().expect("Opaqaue struct must have a name");
                Ok(iwctx.opaque_struct_type(name.as_str()).as_any_type_enum())
            } else {
                let field_types = self
                    .fields()
                    .map(|fty| {
                         let ty = convert_type(ctx, iwctx, fty)?;
                         let ty_basic: BasicTypeEnum = ty.try_into()
                         .map_err(|_err| {
                            input_error_noloc!(ToLLVMErr::FunctionTypeComponentNotBasic)
                         })?;
                         Ok(ty_basic)
                    })
                    .collect::<Result<Vec<_>>>()?;
                if let Some(name) = self.name() {
                    let str_ty = iwctx.opaque_struct_type(name.as_str());
                    str_ty.set_body(&field_types, false);
                    Ok(str_ty.as_any_type_enum())
                } else {
                    Ok(iwctx.struct_type(&field_types, false).as_any_type_enum())
                }
            }
        }
    }
);

/// Convert a pliron [Type] to inkwell [AnyTypeEnum].
pub fn convert_type<'ctx>(
    ctx: &Context,
    iwctx: &'ctx IWContext,
    ty: Ptr<TypeObj>,
) -> Result<AnyTypeEnum<'ctx>> {
    if let Some(converter) = type_cast::<dyn ToLLVMType>(&**ty.deref(ctx)) {
        return converter.convert(ctx, iwctx);
    }
    input_err_noloc!(ToLLVMErr::MissingTypeConversion(
        ty.deref(ctx).get_type_id().to_string()
    ))
}

fn convert_value_operand<'ctx>(
    cctx: &mut ConversionContext<'ctx>,
    ctx: &Context,
    value: &Value,
) -> Result<AnyValueEnum<'ctx>> {
    match cctx.value_map.get(value) {
        Some(v) => Ok(*v),
        None => {
            input_err_noloc!(ToLLVMErr::UndefinedValue(value.unique_name(ctx)))
        }
    }
}

fn convert_block_operand<'ctx>(
    cctx: &mut ConversionContext<'ctx>,
    ctx: &Context,
    block: Ptr<BasicBlock>,
) -> Result<IWBasicBlock<'ctx>> {
    match cctx.block_map.get(&block) {
        Some(v) => Ok(*v),
        None => {
            input_err_noloc!(ToLLVMErr::UndefinedBlock(block.unique_name(ctx)))
        }
    }
}

macro_rules! to_llvm_value_int_bin_op {
    (
        $op_name:ident, $builder_method:ident
    ) => {
        impl_op_interface! (ToLLVMValue for $op_name {
            fn convert<'ctx>(
                &self,
                ctx: &Context,
                _iwctx: &'ctx IWContext,
                cctx: &mut ConversionContext<'ctx>,
            ) -> Result<AnyValueEnum<'ctx>> {
                let op = self.get_operation().deref(ctx);
                let (lhs, rhs) = (op.get_operand(0), op.get_operand(1));
                let lhs: IntValue = convert_value_operand(cctx, ctx, &lhs)?
                    .try_into()
                    .map_err(|_err| input_error_noloc!(ToLLVMErr::IntOpValueErr))?;
                let rhs: IntValue = convert_value_operand(cctx, ctx, &rhs)?
                    .try_into()
                    .map_err(|_err| input_error_noloc!(ToLLVMErr::IntOpValueErr))?;
                let iw_op = cctx
                    .builder
                    .$builder_method(lhs, rhs, &self.get_result(ctx).unique_name(ctx))
                    .map_err(|err| input_error!(op.loc(), err))?;
                Ok(iw_op.as_any_value_enum())
            }
        });
    };
}

to_llvm_value_int_bin_op!(AddOp, build_int_add);
to_llvm_value_int_bin_op!(SubOp, build_int_sub);
to_llvm_value_int_bin_op!(MulOp, build_int_mul);
to_llvm_value_int_bin_op!(SDivOp, build_int_signed_div);
to_llvm_value_int_bin_op!(UDivOp, build_int_unsigned_div);
to_llvm_value_int_bin_op!(URemOp, build_int_unsigned_rem);
to_llvm_value_int_bin_op!(SRemOp, build_int_signed_rem);
to_llvm_value_int_bin_op!(AndOp, build_and);
to_llvm_value_int_bin_op!(OrOp, build_or);
to_llvm_value_int_bin_op!(XorOp, build_xor);
to_llvm_value_int_bin_op!(ShlOp, build_left_shift);

impl_op_interface! (ToLLVMValue for AllocaOp {
    fn convert<'ctx>(
        &self,
        ctx: &Context,
        iwctx: &'ctx IWContext,
        cctx: &mut ConversionContext<'ctx>,
    ) -> Result<AnyValueEnum<'ctx>> {
        let op = self.get_operation().deref(ctx);
        let ty: BasicTypeEnum = convert_type(ctx, iwctx, self.result_pointee_type(ctx))?
            .try_into()
            .map_err(|_err| input_error_noloc!(ToLLVMErr::AllocaOpTypeNotBasic))?;
        let size: IntValue = convert_value_operand(cctx, ctx, &self.get_operand(ctx))?
            .try_into()
            .map_err(|_err| input_error!(op.loc(), ToLLVMErr::AllocaOpSizeNotInt))?;
        let alloca_op = cctx
            .builder
            .build_array_alloca(ty, size, &self.get_result(ctx).unique_name(ctx))
            .map_err(|err| input_error!(op.loc(), err))?;
        Ok(alloca_op.as_any_value_enum())
    }
});

impl_op_interface! (ToLLVMValue for BitcastOp {
    fn convert<'ctx>(
        &self,
        ctx: &Context,
        iwctx: &'ctx IWContext,
        cctx: &mut ConversionContext<'ctx>,
    ) -> Result<AnyValueEnum<'ctx>> {
        let op = self.get_operation().deref(ctx);
        let arg: BasicValueEnum = convert_value_operand(cctx, ctx, &self.get_operand(ctx))?
            .try_into()
            .map_err(|_err| input_error!(op.loc(), ToLLVMErr::BitcastOpOpdNotBasic))?;
        let ty: BasicTypeEnum = convert_type(ctx, iwctx, self.result_type(ctx))?
            .try_into()
            .map_err(|_err| input_error_noloc!(ToLLVMErr::BitcastOpResultNotBasicType))?;
        let bitcast_op = cctx
            .builder
            .build_bitcast(arg, ty, &self.get_result(ctx).unique_name(ctx))
            .map_err(|err| input_error!(op.loc(), err))?;
        Ok(bitcast_op.as_any_value_enum())
    }
});

fn link_succ_operands_with_phis(
    ctx: &Context,
    cctx: &mut ConversionContext<'_>,
    source_block: Ptr<BasicBlock>,
    target_block: IWBasicBlock,
    opds: Vec<Value>,
) -> Result<()> {
    let mut phis = vec![];
    for inst in target_block.get_instructions() {
        let Ok(phi) = TryInto::<PhiValue>::try_into(inst) else {
            break;
        };
        phis.push(phi);
    }

    if phis.len() != opds.len() {
        return input_err!(
            source_block.deref(ctx).loc(),
            ToLLVMErr::NumBlockArgsNumPhisMismatch
        );
    }

    let source_block_iw = convert_block_operand(cctx, ctx, source_block)?;

    for (idx, arg) in opds.iter().enumerate() {
        let arg_iw: BasicValueEnum = convert_value_operand(cctx, ctx, arg)?
            .try_into()
            .map_err(|_err| input_error_noloc!(ToLLVMErr::BranchArgNotBasic))?;
        phis[idx].add_incoming(&[(&arg_iw, source_block_iw)]);
    }
    Ok(())
}

impl_op_interface! (ToLLVMValue for BrOp {
    fn convert<'ctx>(
        &self,
        ctx: &Context,
        _iwctx: &'ctx IWContext,
        cctx: &mut ConversionContext<'ctx>,
    ) -> Result<AnyValueEnum<'ctx>> {
        let op = self.get_operation().deref(ctx);
        let succ = op.get_successor(0);
        let succ_iw = convert_block_operand(cctx, ctx, succ)?;
        let branch_op = cctx
            .builder
            .build_unconditional_branch(succ_iw)
            .map_err(|err| input_error!(op.loc(), err))?;

        // Link the arguments we pass to the block with the PHIs there.
        link_succ_operands_with_phis(
            ctx,
            cctx,
            op.get_container().expect("Unlinked operation"),
            succ_iw,
            self.successor_operands(ctx, 0),
        )?;

        Ok(branch_op.as_any_value_enum())
    }
});

impl_op_interface! (ToLLVMValue for CondBrOp {
    fn convert<'ctx>(
        &self,
        ctx: &Context,
        _iwctx: &'ctx IWContext,
        cctx: &mut ConversionContext<'ctx>,
    ) -> Result<AnyValueEnum<'ctx>> {
        let op = self.get_operation().deref(ctx);
        let (true_succ, false_succ) = (op.get_successor(0), op.get_successor(1));
        let true_succ_iw = convert_block_operand(cctx, ctx, true_succ)?;
        let false_succ_iw = convert_block_operand(cctx, ctx, false_succ)?;
        let cond: IntValue = convert_value_operand(cctx, ctx, &self.condition(ctx))?
            .try_into()
            .map_err(|_err| input_error!(op.loc(), ToLLVMErr::CondBranchCondNotInt))?;

        let branch_op = cctx
            .builder
            .build_conditional_branch(cond, true_succ_iw, false_succ_iw)
            .map_err(|err| input_error!(op.loc(), err))?;

        // Link the arguments we pass to the block with the PHIs there.
        link_succ_operands_with_phis(
            ctx,
            cctx,
            op.get_container().expect("Unlinked operation"),
            true_succ_iw,
            self.successor_operands(ctx, 0),
        )?;
        link_succ_operands_with_phis(
            ctx,
            cctx,
            op.get_container().expect("Unlinked operation"),
            false_succ_iw,
            self.successor_operands(ctx, 1),
        )?;

        Ok(branch_op.as_any_value_enum())
    }
});

impl_op_interface! (ToLLVMValue for LoadOp {
    fn convert<'ctx>(
        &self,
        ctx: &Context,
        iwctx: &'ctx IWContext,
        cctx: &mut ConversionContext<'ctx>,
    ) -> Result<AnyValueEnum<'ctx>> {
        let op = self.get_operation().deref(ctx);
        let pointee_ty: BasicTypeEnum = convert_type(ctx, iwctx, self.result_type(ctx))?
            .try_into()
            .map_err(|_err| input_error!(op.loc(), ToLLVMErr::LoadedValueNotBasicType))?;
        let ptr: PointerValue = convert_value_operand(cctx, ctx, &self.get_operand(ctx))?
            .try_into()
            .map_err(|_err| input_error!(op.loc(), ToLLVMErr::LoadOpdNotPointer))?;
        let load_op = cctx
            .builder
            .build_load(pointee_ty, ptr, &self.get_result(ctx).unique_name(ctx))
            .map_err(|err| input_error!(op.loc(), err))?;
        Ok(load_op.as_any_value_enum())
    }
});

impl_op_interface! (ToLLVMValue for StoreOp {
    fn convert<'ctx>(
        &self,
        ctx: &Context,
        _iwctx: &'ctx IWContext,
        cctx: &mut ConversionContext<'ctx>,
    ) -> Result<AnyValueEnum<'ctx>> {
        let op = self.get_operation().deref(ctx);
        let value: BasicValueEnum = convert_value_operand(cctx, ctx, &self.value_opd(ctx))?
            .try_into()
            .map_err(|_err| input_error!(op.loc(), ToLLVMErr::StoredValueNotBasicType))?;
        let ptr: PointerValue = convert_value_operand(cctx, ctx, &self.address_opd(ctx))?
            .try_into()
            .map_err(|_err| input_error!(op.loc(), ToLLVMErr::StorePointerIncorrect))?;
        let store_op = cctx
            .builder
            .build_store(ptr, value)
            .map_err(|err| input_error!(op.loc(), err))?;
        Ok(store_op.as_any_value_enum())
    }
});

impl_op_interface! (ToLLVMValue for ICmpOp {
    fn convert<'ctx>(
        &self,
        ctx: &Context,
        _iwctx: &'ctx IWContext,
        cctx: &mut ConversionContext<'ctx>,
    ) -> Result<AnyValueEnum<'ctx>> {
        let op = self.get_operation().deref(ctx);
        let predicate = convert_ipredicate(self.predicate(ctx));
        let lhs: IntValue = convert_value_operand(cctx, ctx, &op.get_operand(0))?
            .try_into()
            .map_err(|_err| input_error!(op.loc(), ToLLVMErr::ICmpOpOpdNotInt))?;
        let rhs: IntValue = convert_value_operand(cctx, ctx, &op.get_operand(1))?
            .try_into()
            .map_err(|_err| input_error!(op.loc(), ToLLVMErr::ICmpOpOpdNotInt))?;
        let icmp_op = cctx
            .builder
            .build_int_compare(predicate, lhs, rhs, &self.get_result(ctx).unique_name(ctx))
        .map_err(|err| input_error!(op.loc(), err))?;
        Ok(icmp_op.as_any_value_enum())
    }
});

impl_op_interface! (ToLLVMValue for ReturnOp {
    fn convert<'ctx>(
        &self,
        ctx: &Context,
        _iwctx: &'ctx IWContext,
        cctx: &mut ConversionContext<'ctx>,
    ) -> Result<AnyValueEnum<'ctx>> {
        let op = self.get_operation().deref(ctx);
        let ret_op =
            if let Some(retval) = self.retval(ctx) {
                let retval: BasicValueEnum = convert_value_operand(cctx, ctx, &retval)?
                .try_into()
                .map_err(|_err| input_error!(op.loc(), ToLLVMErr::ReturnOpOperandNotBasic))?;
                cctx.builder.build_return
                    (Some(&retval)).map_err(|err| input_error!(op.loc(), err))?
            } else {
                cctx.builder.build_return(None).map_err(|err| input_error!(op.loc(), err))?
            };
        Ok(ret_op.as_any_value_enum())
    }
});

impl_op_interface! (ToLLVMValue for ConstantOp {
    fn convert<'ctx>(
        &self,
        ctx: &Context,
        iwctx: &'ctx IWContext,
        _cctx: &mut ConversionContext<'ctx>,
    ) -> Result<AnyValueEnum<'ctx>> {
        let op = self.get_operation().deref(ctx);
        let value = self.get_value(ctx);
        if let Some(int_val) = value.downcast_ref::<IntegerAttr>() {
            let int_ty = TypePtr::<IntegerType>::from_ptr(int_val.get_type(ctx), ctx).unwrap();
            let int_ty_iw: iwtypes::IntType =
                convert_type(ctx, iwctx, int_ty.into())?
                .try_into()
                .map_err(|_err| input_error!(op.loc(), ToLLVMErr::ConstOpNotIntOrFloat))?;
            let ap_int_val: ApInt = int_val.clone().into();
            let const_val =
                int_ty_iw.const_int(ap_int_val.resize_to_u64(), false);
            Ok(const_val.as_any_value_enum())
        } else if let Some(_float_val) = value.downcast_ref::<FloatAttr>() {
            todo!()
        } else {
            input_err!(op.loc(), ToLLVMErr::ConstOpNotIntOrFloat)
        }
    }
});

impl_op_interface! (ToLLVMValue for UndefOp {
    fn convert<'ctx>(
        &self,
        ctx: &Context,
        iwctx: &'ctx IWContext,
        _cctx: &mut ConversionContext<'ctx>,
    ) -> Result<AnyValueEnum<'ctx>> {
        let ty = convert_type(ctx, iwctx, self.result_type(ctx))?;
        if let Ok(int_ty) = TryInto::<IntType>::try_into(ty) {
            Ok(int_ty.get_undef().as_any_value_enum())
        } else {
            todo!()
        }
    }
});

/// Conver a pliron [BasicBlock] to inkwell [BasicBlock][IWBasicBlock].
fn convert_block<'ctx>(
    ctx: &Context,
    iwctx: &'ctx IWContext,
    cctx: &mut ConversionContext<'ctx>,
    block: Ptr<BasicBlock>,
) -> Result<()> {
    let iw_block = cctx.block_map[&block];
    cctx.builder.position_at_end(iw_block);

    for (op, loc) in block
        .deref(ctx)
        .iter(ctx)
        .map(|op| (Operation::get_op(op, ctx), op.deref(ctx).loc()))
    {
        let Some(op_conv) = op_cast::<dyn ToLLVMValue>(&*op) else {
            return input_err!(
                loc,
                ToLLVMErr::MissingOpConversion(op.get_opid().to_string())
            );
        };
        let op_iw = op_conv.convert(ctx, iwctx, cctx)?;
        let op_ref = &*op.get_operation().deref(ctx);
        // LLVM instructions have at most one result.
        if op_ref.get_num_results() == 1 {
            cctx.value_map.insert(op_ref.get_result(0), op_iw);
        }
    }

    Ok(())
}

/// Convert a pliron [FuncOp] to inkwell [FunctionValue]
fn convert_function<'ctx>(
    ctx: &Context,
    iwctx: &'ctx IWContext,
    module_iw: &IWModule<'ctx>,
    func_op: FuncOp,
) -> Result<FunctionValue<'ctx>> {
    let func_ty = func_op.get_type(ctx).deref(ctx);
    let func_ty_to_iw = type_cast::<dyn ToLLVMType>(&**func_ty)
        .ok_or(input_error_noloc!(ToLLVMErr::FuncOpTypeErr))?;
    let ty = func_ty_to_iw.convert(ctx, iwctx)?;
    let func_ty: iwtypes::FunctionType = ty
        .try_into()
        .map_err(|_err| input_error_noloc!(ToLLVMErr::FuncOpTypeErr))?;

    let cctx = &mut ConversionContext::new(iwctx);
    let func_iw = module_iw.add_function(&func_op.get_symbol_name(ctx), func_ty, None);

    // Map all blocks, staring with entry.
    let mut block_iter = func_op.get_region(ctx).deref(ctx).iter(ctx);
    {
        let entry = block_iter.next().expect("Missing entry block");
        assert!(entry == func_op.get_entry_block(ctx));
        // Map entry block arguments to inkwell function arguments.
        for (arg_idx, arg) in entry.deref(ctx).arguments().enumerate() {
            cctx.value_map.insert(
                arg,
                func_iw
                    .get_nth_param(arg_idx.try_into().unwrap())
                    .unwrap()
                    .as_any_value_enum(),
            );
        }
        let iw_entry_block = iwctx.append_basic_block(func_iw, &entry.deref(ctx).unique_name(ctx));
        cctx.block_map.insert(entry, iw_entry_block);
    }
    for block in block_iter {
        let iw_block = iwctx.append_basic_block(func_iw, &block.deref(ctx).unique_name(ctx));
        let builder = iwctx.create_builder();
        builder.position_at_end(iw_block);
        for arg in block.deref(ctx).arguments() {
            let arg_type: BasicTypeEnum =
                convert_type(ctx, iwctx, arg.get_type(ctx))?
                    .try_into()
                    .map_err(|_err| input_error_noloc!(ToLLVMErr::PhiTypeNotBasic))?;
            let phi = builder
                .build_phi(arg_type, &arg.unique_name(ctx))
                .map_err(|err| input_error_noloc!(err))?;
            cctx.value_map.insert(arg, phi.as_any_value_enum());
        }
        cctx.block_map.insert(block, iw_block);
    }

    // Convert within every block.
    for block in topological_order(ctx, func_op.get_region(ctx)) {
        convert_block(ctx, iwctx, cctx, block)?;
    }

    Ok(func_iw)
}

/// Convert pliron [ModuleOp] to inkwell [Module](IWModule).
pub fn convert_module<'ctx>(
    ctx: &Context,
    iwctx: &'ctx IWContext,
    module: ModuleOp,
) -> Result<IWModule<'ctx>> {
    let mod_name = module.get_symbol_name(ctx);
    let module_iw = iwctx.create_module(&mod_name);

    for op in module.get_body(ctx, 0).deref(ctx).iter(ctx) {
        if let Some(func_op) = Operation::get_op(op, ctx).downcast_ref::<FuncOp>() {
            convert_function(ctx, iwctx, &module_iw, *func_op)?;
        }
        // TODO: Globals
    }

    Ok(module_iw)
}
