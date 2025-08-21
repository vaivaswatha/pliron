//! Translate from pliron's LLVM dialect to LLVM-IR

use llvm_sys::LLVMIntPredicate;
use pliron::{
    basic_block::BasicBlock,
    builtin::{
        attributes::IntegerAttr,
        op_interfaces::{
            BranchOpInterface, CallOpCallable, CallOpInterface, OneOpdInterface,
            OneRegionInterface, OneResultInterface, SingleBlockRegionInterface, SymbolOpInterface,
        },
        ops::{FuncOp, ModuleOp},
        types::{FunctionType, IntegerType},
    },
    common_traits::Named,
    context::{Context, Ptr},
    graph::traversals::region::topological_order,
    identifier::Identifier,
    input_err, input_err_noloc, input_error, input_error_noloc,
    linked_list::{ContainsLinkedList, LinkedList},
    location::Located,
    op::{Op, op_cast},
    operation::Operation,
    result::Result,
    r#type::{Type, TypeObj, Typed, type_cast},
    utils::apint::APInt,
    value::Value,
};

use pliron::derive::{op_interface, op_interface_impl, type_interface, type_interface_impl};
use rustc_hash::FxHashMap;
use thiserror::Error;

use crate::{
    attributes::ICmpPredicateAttr,
    llvm_sys::core::{
        LLVMBasicBlock, LLVMBuilder, LLVMContext, LLVMModule, LLVMType, LLVMValue,
        instruction_iter, llvm_add_case, llvm_add_function, llvm_add_global, llvm_add_incoming,
        llvm_append_basic_block_in_context, llvm_array_type2, llvm_build_add, llvm_build_and,
        llvm_build_array_alloca, llvm_build_bitcast, llvm_build_br, llvm_build_call2,
        llvm_build_cond_br, llvm_build_extract_value, llvm_build_gep2, llvm_build_icmp,
        llvm_build_insert_value, llvm_build_int_to_ptr, llvm_build_load2, llvm_build_mul,
        llvm_build_or, llvm_build_phi, llvm_build_ptr_to_int, llvm_build_ret, llvm_build_ret_void,
        llvm_build_sdiv, llvm_build_select, llvm_build_sext, llvm_build_shl, llvm_build_srem,
        llvm_build_store, llvm_build_sub, llvm_build_switch, llvm_build_trunc, llvm_build_udiv,
        llvm_build_urem, llvm_build_xor, llvm_clear_insertion_position, llvm_const_int,
        llvm_const_null, llvm_delete_function, llvm_function_type, llvm_get_param, llvm_get_undef,
        llvm_int_type_in_context, llvm_is_a, llvm_pointer_type_in_context,
        llvm_position_builder_at_end, llvm_set_initializer, llvm_struct_create_named,
        llvm_struct_set_body, llvm_struct_type_in_context, llvm_void_type_in_context,
    },
    op_interfaces::PointerTypeResult,
    ops::{
        AddOp, AddressOfOp, AllocaOp, AndOp, BitcastOp, BrOp, CallOp, CondBrOp, ConstantOp,
        ExtractValueOp, GetElementPtrOp, GlobalOp, ICmpOp, InsertValueOp, IntToPtrOp, LoadOp,
        MulOp, OrOp, PtrToIntOp, ReturnOp, SDivOp, SExtOp, SRemOp, SelectOp, ShlOp, StoreOp, SubOp,
        SwitchOp, TruncOp, UDivOp, URemOp, UndefOp, XorOp, ZExtOp, ZeroOp,
    },
    types::{ArrayType, PointerType, StructType, VoidType},
};

/// Mapping from pliron entities to LLVM entities.
pub struct ConversionContext {
    // A map from pliron Values to LLVM Values.
    value_map: FxHashMap<Value, LLVMValue>,
    // A map from pliron basic blocks to LLVM.
    block_map: FxHashMap<Ptr<BasicBlock>, LLVMBasicBlock>,
    // A map from pliron functions to LLVM functions.
    function_map: FxHashMap<Identifier, LLVMValue>,
    // A map from pliron globals to LLVM globals.
    globals_map: FxHashMap<Identifier, LLVMValue>,
    // The active LLVM builder.
    builder: LLVMBuilder,
    // Scratch builder in a scratch function for attempting to evaluate constants.
    scratch_builder: LLVMBuilder,
}

impl ConversionContext {
    pub fn new(llvm_ctx: &LLVMContext) -> Self {
        Self {
            value_map: FxHashMap::default(),
            block_map: FxHashMap::default(),
            function_map: FxHashMap::default(),
            globals_map: FxHashMap::default(),
            builder: LLVMBuilder::new(llvm_ctx),
            scratch_builder: LLVMBuilder::new(llvm_ctx),
        }
    }

    pub fn clear_per_function_data(&mut self) {
        self.value_map.clear();
        self.block_map.clear();
        llvm_clear_insertion_position(&self.builder);
    }
}

#[derive(Error, Debug)]
pub enum ToLLVMErr {
    #[error("Type {0} does not have a conversion to LLVM type implemented")]
    MissingTypeConversion(String),
    #[error("Operation {0} does not have a conversion to LLVM instruction implemented")]
    MissingOpConversion(String),
    #[error("Definition for value {0} not seen yet")]
    UndefinedValue(String),
    #[error("Block definition {0} not seen yet")]
    UndefinedBlock(String),
    #[error("Number of block args in the source dialect equal the number of PHIs in target IR")]
    NumBlockArgsNumPhisMismatch,
    #[error("ConstantOp must have integer or float value")]
    ConstOpNotIntOrFloat,
    #[error(
        "Insert/Extract value instructions must specify exactly one index, an LLVM-C API limitation"
    )]
    InsertExtractValueIndices,
    #[error("GlobalOp Initializer region does not terminate with a return with value")]
    GlobalOpInitializerRegionBadReturn,
    #[error("Cannot evaluate value to a constant")]
    CannotEvaluateToConst,
}

pub fn convert_ipredicate(pred: ICmpPredicateAttr) -> LLVMIntPredicate {
    match pred {
        ICmpPredicateAttr::EQ => LLVMIntPredicate::LLVMIntEQ,
        ICmpPredicateAttr::NE => LLVMIntPredicate::LLVMIntNE,
        ICmpPredicateAttr::UGT => LLVMIntPredicate::LLVMIntUGT,
        ICmpPredicateAttr::UGE => LLVMIntPredicate::LLVMIntUGE,
        ICmpPredicateAttr::ULT => LLVMIntPredicate::LLVMIntULT,
        ICmpPredicateAttr::ULE => LLVMIntPredicate::LLVMIntULE,
        ICmpPredicateAttr::SGT => LLVMIntPredicate::LLVMIntSGT,
        ICmpPredicateAttr::SGE => LLVMIntPredicate::LLVMIntSGE,
        ICmpPredicateAttr::SLT => LLVMIntPredicate::LLVMIntSLT,
        ICmpPredicateAttr::SLE => LLVMIntPredicate::LLVMIntSLE,
    }
}

/// A type that implements this is convertible to an [LLVMType].
#[type_interface]
trait ToLLVMType {
    /// Convert from pliron [Type] to [LLVMType].
    fn convert(&self, ctx: &Context, llvm_ctx: &LLVMContext) -> Result<LLVMType>;

    fn verify(_type: &dyn Type, _ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        Ok(())
    }
}

/// An [Op] that implements this is convertible to an [LLVMValue].
#[op_interface]
trait ToLLVMValue {
    /// Convert from pliron [Op] to [LLVMValue].
    fn convert(
        &self,
        ctx: &Context,
        llvm_ctx: &LLVMContext,
        cctx: &mut ConversionContext,
    ) -> Result<LLVMValue>;

    fn verify(_op: &dyn Op, _ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        Ok(())
    }
}

#[type_interface_impl]
impl ToLLVMType for IntegerType {
    fn convert(&self, _ctx: &Context, llvm_ctx: &LLVMContext) -> Result<LLVMType> {
        Ok(llvm_int_type_in_context(llvm_ctx, self.get_width()))
    }
}

#[type_interface_impl]
impl ToLLVMType for ArrayType {
    fn convert(&self, ctx: &Context, llvm_ctx: &LLVMContext) -> Result<LLVMType> {
        let elem_ty = convert_type(ctx, llvm_ctx, self.elem_type())?;
        Ok(llvm_array_type2(elem_ty, self.size()))
    }
}

#[type_interface_impl]
impl ToLLVMType for FunctionType {
    fn convert(&self, ctx: &Context, llvm_ctx: &LLVMContext) -> Result<LLVMType> {
        let args_tys: Vec<_> = self
            .get_inputs()
            .iter()
            .map(|ty| convert_type(ctx, llvm_ctx, *ty))
            .collect::<Result<_>>()?;
        let ret_ty = self
            .get_results()
            .first()
            .map(|ty| convert_type(ctx, llvm_ctx, *ty))
            .unwrap_or(Ok(llvm_void_type_in_context(llvm_ctx)))?;
        Ok(llvm_function_type(ret_ty, &args_tys, false))
    }
}

#[type_interface_impl]
impl ToLLVMType for VoidType {
    fn convert(&self, _ctx: &Context, llvm_ctx: &LLVMContext) -> Result<LLVMType> {
        Ok(llvm_void_type_in_context(llvm_ctx))
    }
}

#[type_interface_impl]
impl ToLLVMType for PointerType {
    fn convert(&self, _ctx: &Context, llvm_ctx: &LLVMContext) -> Result<LLVMType> {
        Ok(llvm_pointer_type_in_context(llvm_ctx, 0))
    }
}

#[type_interface_impl]
impl ToLLVMType for StructType {
    fn convert(&self, ctx: &Context, llvm_ctx: &LLVMContext) -> Result<LLVMType> {
        if self.is_opaque() {
            let name = self.name().expect("Opaqaue struct must have a name");
            Ok(llvm_struct_create_named(llvm_ctx, name.as_str()))
        } else {
            let field_types = self
                .fields()
                .map(|fty| convert_type(ctx, llvm_ctx, fty))
                .collect::<Result<Vec<_>>>()?;
            if let Some(name) = self.name() {
                let str_ty = llvm_struct_create_named(llvm_ctx, name.as_str());
                llvm_struct_set_body(str_ty, &field_types, false);
                Ok(str_ty)
            } else {
                Ok(llvm_struct_type_in_context(llvm_ctx, &field_types, false))
            }
        }
    }
}

/// Convert a pliron [Type] to [LLVMType].
pub fn convert_type(ctx: &Context, llvm_ctx: &LLVMContext, ty: Ptr<TypeObj>) -> Result<LLVMType> {
    if let Some(converter) = type_cast::<dyn ToLLVMType>(&**ty.deref(ctx)) {
        return converter.convert(ctx, llvm_ctx);
    }
    input_err_noloc!(ToLLVMErr::MissingTypeConversion(
        ty.deref(ctx).get_type_id().to_string()
    ))
}

fn convert_value_operand(
    cctx: &mut ConversionContext,
    ctx: &Context,
    value: &Value,
) -> Result<LLVMValue> {
    match cctx.value_map.get(value) {
        Some(v) => Ok(*v),
        None => {
            input_err_noloc!(ToLLVMErr::UndefinedValue(value.unique_name(ctx).into()))
        }
    }
}

fn convert_block_operand(
    cctx: &mut ConversionContext,
    ctx: &Context,
    block: Ptr<BasicBlock>,
) -> Result<LLVMBasicBlock> {
    match cctx.block_map.get(&block) {
        Some(v) => Ok(*v),
        None => {
            input_err_noloc!(ToLLVMErr::UndefinedBlock(block.unique_name(ctx).into()))
        }
    }
}

macro_rules! to_llvm_value_int_bin_op {
    (
        $op_name:ident, $builder_function:ident
    ) => {
        #[pliron::derive::op_interface_impl]
        impl ToLLVMValue for $op_name {
            fn convert(
                &self,
                ctx: &Context,
                _llvm_ctx: &LLVMContext,
                cctx: &mut ConversionContext,
            ) -> Result<LLVMValue> {
                let op = self.get_operation().deref(ctx);
                let (lhs, rhs) = (op.get_operand(0), op.get_operand(1));
                let lhs = convert_value_operand(cctx, ctx, &lhs)?;
                let rhs = convert_value_operand(cctx, ctx, &rhs)?;
                Ok($builder_function(
                    &cctx.builder,
                    lhs,
                    rhs,
                    &self.get_result(ctx).unique_name(ctx),
                ))
            }
        }
    };
}

to_llvm_value_int_bin_op!(AddOp, llvm_build_add);
to_llvm_value_int_bin_op!(SubOp, llvm_build_sub);
to_llvm_value_int_bin_op!(MulOp, llvm_build_mul);
to_llvm_value_int_bin_op!(SDivOp, llvm_build_sdiv);
to_llvm_value_int_bin_op!(UDivOp, llvm_build_udiv);
to_llvm_value_int_bin_op!(URemOp, llvm_build_urem);
to_llvm_value_int_bin_op!(SRemOp, llvm_build_srem);
to_llvm_value_int_bin_op!(AndOp, llvm_build_and);
to_llvm_value_int_bin_op!(OrOp, llvm_build_or);
to_llvm_value_int_bin_op!(XorOp, llvm_build_xor);
to_llvm_value_int_bin_op!(ShlOp, llvm_build_shl);

#[op_interface_impl]
impl ToLLVMValue for AllocaOp {
    fn convert(
        &self,
        ctx: &Context,
        llvm_ctx: &LLVMContext,
        cctx: &mut ConversionContext,
    ) -> Result<LLVMValue> {
        let ty = convert_type(ctx, llvm_ctx, self.result_pointee_type(ctx))?;
        let size = convert_value_operand(cctx, ctx, &self.get_operand(ctx))?;
        let alloca_op = llvm_build_array_alloca(
            &cctx.builder,
            ty,
            size,
            &self.get_result(ctx).unique_name(ctx),
        );
        Ok(alloca_op)
    }
}

#[op_interface_impl]
impl ToLLVMValue for BitcastOp {
    fn convert(
        &self,
        ctx: &Context,
        llvm_ctx: &LLVMContext,
        cctx: &mut ConversionContext,
    ) -> Result<LLVMValue> {
        let arg = convert_value_operand(cctx, ctx, &self.get_operand(ctx))?;
        let ty = convert_type(ctx, llvm_ctx, self.result_type(ctx))?;
        let bitcast_op = llvm_build_bitcast(
            &cctx.builder,
            arg,
            ty,
            &self.get_result(ctx).unique_name(ctx),
        );
        Ok(bitcast_op)
    }
}

fn link_succ_operands_with_phis(
    ctx: &Context,
    cctx: &mut ConversionContext,
    source_block: Ptr<BasicBlock>,
    target_block: LLVMBasicBlock,
    opds: Vec<Value>,
) -> Result<()> {
    let mut phis = vec![];
    for inst in instruction_iter(target_block) {
        if !llvm_is_a::phi_node(inst) {
            break;
        };
        phis.push(inst);
    }

    if phis.len() != opds.len() {
        return input_err!(
            source_block.deref(ctx).loc(),
            ToLLVMErr::NumBlockArgsNumPhisMismatch
        );
    }

    let source_block = convert_block_operand(cctx, ctx, source_block)?;

    for (idx, arg) in opds.iter().enumerate() {
        let arg = convert_value_operand(cctx, ctx, arg)?;
        llvm_add_incoming(phis[idx], &[arg], &[source_block]);
    }
    Ok(())
}

#[op_interface_impl]
impl ToLLVMValue for BrOp {
    fn convert(
        &self,
        ctx: &Context,
        _llvm_ctx: &LLVMContext,
        cctx: &mut ConversionContext,
    ) -> Result<LLVMValue> {
        let op = self.get_operation().deref(ctx);
        let succ = op.get_successor(0);
        let succ_llvm = convert_block_operand(cctx, ctx, succ)?;
        let branch_op = llvm_build_br(&cctx.builder, succ_llvm);

        // Link the arguments we pass to the block with the PHIs there.
        link_succ_operands_with_phis(
            ctx,
            cctx,
            op.get_container().expect("Unlinked operation"),
            succ_llvm,
            self.successor_operands(ctx, 0),
        )?;

        Ok(branch_op)
    }
}

#[op_interface_impl]
impl ToLLVMValue for CondBrOp {
    fn convert(
        &self,
        ctx: &Context,
        _llvm_ctx: &LLVMContext,
        cctx: &mut ConversionContext,
    ) -> Result<LLVMValue> {
        let op = self.get_operation().deref(ctx);
        let (true_succ, false_succ) = (op.get_successor(0), op.get_successor(1));
        let true_succ_llvm = convert_block_operand(cctx, ctx, true_succ)?;
        let false_succ_llvm = convert_block_operand(cctx, ctx, false_succ)?;
        let cond = convert_value_operand(cctx, ctx, &self.condition(ctx))?;

        let branch_op = llvm_build_cond_br(&cctx.builder, cond, true_succ_llvm, false_succ_llvm);

        // Link the arguments we pass to the block with the PHIs there.
        link_succ_operands_with_phis(
            ctx,
            cctx,
            op.get_container().expect("Unlinked operation"),
            true_succ_llvm,
            self.successor_operands(ctx, 0),
        )?;
        link_succ_operands_with_phis(
            ctx,
            cctx,
            op.get_container().expect("Unlinked operation"),
            false_succ_llvm,
            self.successor_operands(ctx, 1),
        )?;

        Ok(branch_op)
    }
}

#[op_interface_impl]
impl ToLLVMValue for SwitchOp {
    fn convert(
        &self,
        ctx: &Context,
        llvm_ctx: &LLVMContext,
        cctx: &mut ConversionContext,
    ) -> Result<LLVMValue> {
        let op = self.get_operation().deref(ctx);
        let cond = convert_value_operand(cctx, ctx, &self.condition(ctx))?;
        let default_succ = convert_block_operand(cctx, ctx, self.default_dest(ctx))?;
        let switch_op = llvm_build_switch(
            &cctx.builder,
            cond,
            default_succ,
            self.cases(ctx).len() as u32,
        );

        // Link the arguments we pass to the block with the PHIs there.
        for case in self.cases(ctx) {
            let succ_llvm = convert_block_operand(cctx, ctx, case.dest)?;
            link_succ_operands_with_phis(
                ctx,
                cctx,
                op.get_container().expect("Unlinked operation"),
                succ_llvm,
                case.dest_opds,
            )?;

            let int_ty = case.value.get_type();
            let int_ty_llvm = convert_type(ctx, llvm_ctx, int_ty.into())?;
            let ap_int_val: APInt = case.value.clone().into();
            let case_const_val = llvm_const_int(int_ty_llvm, ap_int_val.to_u64(), false);

            llvm_add_case(switch_op, case_const_val, succ_llvm);
        }

        Ok(switch_op)
    }
}

#[op_interface_impl]
impl ToLLVMValue for LoadOp {
    fn convert(
        &self,
        ctx: &Context,
        llvm_ctx: &LLVMContext,
        cctx: &mut ConversionContext,
    ) -> Result<LLVMValue> {
        let pointee_ty = convert_type(ctx, llvm_ctx, self.result_type(ctx))?;
        let ptr = convert_value_operand(cctx, ctx, &self.get_operand(ctx))?;
        let load_op = llvm_build_load2(
            &cctx.builder,
            pointee_ty,
            ptr,
            &self.get_result(ctx).unique_name(ctx),
        );
        Ok(load_op)
    }
}

#[op_interface_impl]
impl ToLLVMValue for StoreOp {
    fn convert(
        &self,
        ctx: &Context,
        _llvm_ctx: &LLVMContext,
        cctx: &mut ConversionContext,
    ) -> Result<LLVMValue> {
        let value = convert_value_operand(cctx, ctx, &self.value_opd(ctx))?;
        let ptr = convert_value_operand(cctx, ctx, &self.address_opd(ctx))?;
        let store_op = llvm_build_store(&cctx.builder, value, ptr);
        Ok(store_op)
    }
}

#[op_interface_impl]
impl ToLLVMValue for ICmpOp {
    fn convert(
        &self,
        ctx: &Context,
        _llvm_ctx: &LLVMContext,
        cctx: &mut ConversionContext,
    ) -> Result<LLVMValue> {
        let op = self.get_operation().deref(ctx);
        let predicate = convert_ipredicate(self.predicate(ctx));
        let lhs = convert_value_operand(cctx, ctx, &op.get_operand(0))?;
        let rhs = convert_value_operand(cctx, ctx, &op.get_operand(1))?;
        let icmp_op = llvm_build_icmp(
            &cctx.builder,
            predicate,
            lhs,
            rhs,
            &self.get_result(ctx).unique_name(ctx),
        );
        Ok(icmp_op)
    }
}

#[op_interface_impl]
impl ToLLVMValue for ReturnOp {
    fn convert(
        &self,
        ctx: &Context,
        _llvm_ctx: &LLVMContext,
        cctx: &mut ConversionContext,
    ) -> Result<LLVMValue> {
        let ret_op = if let Some(retval) = self.retval(ctx) {
            let retval = convert_value_operand(cctx, ctx, &retval)?;
            llvm_build_ret(&cctx.builder, retval)
        } else {
            llvm_build_ret_void(&cctx.builder)
        };
        Ok(ret_op)
    }
}

#[op_interface_impl]
impl ToLLVMValue for ConstantOp {
    fn convert(
        &self,
        ctx: &Context,
        llvm_ctx: &LLVMContext,
        cctx: &mut ConversionContext,
    ) -> Result<LLVMValue> {
        <Self as ToLLVMConstValue>::convert(self, ctx, llvm_ctx, cctx)
    }
}

#[op_interface_impl]
impl ToLLVMValue for ZeroOp {
    fn convert(
        &self,
        ctx: &Context,
        llvm_ctx: &LLVMContext,
        cctx: &mut ConversionContext,
    ) -> Result<LLVMValue> {
        <Self as ToLLVMConstValue>::convert(self, ctx, llvm_ctx, cctx)
    }
}

#[op_interface_impl]
impl ToLLVMValue for IntToPtrOp {
    fn convert(
        &self,
        ctx: &Context,
        llvm_ctx: &LLVMContext,
        cctx: &mut ConversionContext,
    ) -> Result<LLVMValue> {
        let op = self.get_operation().deref(ctx);
        let arg = convert_value_operand(cctx, ctx, &op.get_operand(0))?;
        let ty = convert_type(ctx, llvm_ctx, self.result_type(ctx))?;
        let inttoptr_op = llvm_build_int_to_ptr(
            &cctx.builder,
            arg,
            ty,
            &self.get_result(ctx).unique_name(ctx),
        );
        Ok(inttoptr_op)
    }
}

#[op_interface_impl]
impl ToLLVMValue for PtrToIntOp {
    fn convert(
        &self,
        ctx: &Context,
        llvm_ctx: &LLVMContext,
        cctx: &mut ConversionContext,
    ) -> Result<LLVMValue> {
        let op = self.get_operation().deref(ctx);
        let arg = convert_value_operand(cctx, ctx, &op.get_operand(0))?;
        let ty = convert_type(ctx, llvm_ctx, self.result_type(ctx))?;
        let ptrtoint_op = llvm_build_ptr_to_int(
            &cctx.builder,
            arg,
            ty,
            &self.get_result(ctx).unique_name(ctx),
        );
        Ok(ptrtoint_op)
    }
}

#[op_interface_impl]
impl ToLLVMValue for UndefOp {
    fn convert(
        &self,
        ctx: &Context,
        llvm_ctx: &LLVMContext,
        cctx: &mut ConversionContext,
    ) -> Result<LLVMValue> {
        <Self as ToLLVMConstValue>::convert(self, ctx, llvm_ctx, cctx)
    }
}

#[op_interface_impl]
impl ToLLVMValue for AddressOfOp {
    fn convert(
        &self,
        ctx: &Context,
        llvm_ctx: &LLVMContext,
        cctx: &mut ConversionContext,
    ) -> Result<LLVMValue> {
        <Self as ToLLVMConstValue>::convert(self, ctx, llvm_ctx, cctx)
    }
}

#[op_interface_impl]
impl ToLLVMValue for CallOp {
    fn convert(
        &self,
        ctx: &Context,
        llvm_ctx: &LLVMContext,
        cctx: &mut ConversionContext,
    ) -> Result<LLVMValue> {
        if let CallOpCallable::Direct(callee_sym) = self.callee(ctx) {
            let callee = *cctx.function_map.get(&callee_sym).ok_or_else(|| {
                input_error_noloc!(ToLLVMErr::UndefinedValue(callee_sym.to_string()))
            })?;
            let args: Vec<_> = self
                .args(ctx)
                .into_iter()
                .map(|v| convert_value_operand(cctx, ctx, &v))
                .collect::<Result<_>>()?;
            let ty = convert_type(ctx, llvm_ctx, self.callee_type(ctx).into())?;
            let call_val = llvm_build_call2(
                &cctx.builder,
                ty,
                callee,
                &args,
                &self.get_result(ctx).unique_name(ctx),
            );
            Ok(call_val)
        } else {
            todo!()
        }
    }
}

#[op_interface_impl]
impl ToLLVMValue for SExtOp {
    fn convert(
        &self,
        ctx: &Context,
        llvm_ctx: &LLVMContext,
        cctx: &mut ConversionContext,
    ) -> Result<LLVMValue> {
        let op = self.get_operation().deref(ctx);
        let arg = convert_value_operand(cctx, ctx, &op.get_operand(0))?;
        let ty = convert_type(ctx, llvm_ctx, self.result_type(ctx))?;
        let sext_op = llvm_build_sext(
            &cctx.builder,
            arg,
            ty,
            &self.get_result(ctx).unique_name(ctx),
        );
        Ok(sext_op)
    }
}

#[op_interface_impl]
impl ToLLVMValue for ZExtOp {
    fn convert(
        &self,
        ctx: &Context,
        llvm_ctx: &LLVMContext,
        cctx: &mut ConversionContext,
    ) -> Result<LLVMValue> {
        let op = self.get_operation().deref(ctx);
        let arg = convert_value_operand(cctx, ctx, &op.get_operand(0))?;
        let ty = convert_type(ctx, llvm_ctx, self.result_type(ctx))?;
        let zext_op = llvm_build_sext(
            &cctx.builder,
            arg,
            ty,
            &self.get_result(ctx).unique_name(ctx),
        );
        Ok(zext_op)
    }
}

#[op_interface_impl]
impl ToLLVMValue for TruncOp {
    fn convert(
        &self,
        ctx: &Context,
        llvm_ctx: &LLVMContext,
        cctx: &mut ConversionContext,
    ) -> Result<LLVMValue> {
        let op = self.get_operation().deref(ctx);
        let arg = convert_value_operand(cctx, ctx, &op.get_operand(0))?;
        let ty = convert_type(ctx, llvm_ctx, self.result_type(ctx))?;
        let trunc_op = llvm_build_trunc(
            &cctx.builder,
            arg,
            ty,
            &self.get_result(ctx).unique_name(ctx),
        );
        Ok(trunc_op)
    }
}

#[op_interface_impl]
impl ToLLVMValue for GetElementPtrOp {
    fn convert(
        &self,
        ctx: &Context,
        llvm_ctx: &LLVMContext,
        cctx: &mut ConversionContext,
    ) -> Result<LLVMValue> {
        let indices = self
            .indices(ctx)
            .iter()
            .map(|v| match v {
                crate::ops::GepIndex::Constant(c) => Ok(llvm_const_int(
                    llvm_int_type_in_context(llvm_ctx, 32),
                    Into::<u64>::into(*c),
                    false,
                )),
                crate::ops::GepIndex::Value(value) => convert_value_operand(cctx, ctx, value),
            })
            .collect::<Result<Vec<_>>>()?;

        let base = convert_value_operand(cctx, ctx, &self.src_ptr(ctx))?;

        let src_elem_type = convert_type(ctx, llvm_ctx, self.src_elem_type(ctx))?;
        let gep_op = llvm_build_gep2(
            &cctx.builder,
            src_elem_type,
            base,
            &indices,
            &self.get_result(ctx).unique_name(ctx),
        );
        Ok(gep_op)
    }
}

#[op_interface_impl]
impl ToLLVMValue for InsertValueOp {
    fn convert(
        &self,
        ctx: &Context,
        _llvm_ctx: &LLVMContext,
        cctx: &mut ConversionContext,
    ) -> Result<LLVMValue> {
        let op = self.get_operation().deref(ctx);
        let base = convert_value_operand(cctx, ctx, &op.get_operand(0))?;
        let value = convert_value_operand(cctx, ctx, &op.get_operand(1))?;
        let indices = self.indices(ctx);
        if indices.len() != 1 {
            return input_err!(op.loc(), ToLLVMErr::InsertExtractValueIndices);
        }
        let insert_op = llvm_build_insert_value(
            &cctx.builder,
            base,
            value,
            indices[0],
            &self.get_result(ctx).unique_name(ctx),
        );
        Ok(insert_op)
    }
}

#[op_interface_impl]
impl ToLLVMValue for ExtractValueOp {
    fn convert(
        &self,
        ctx: &Context,
        _llvm_ctx: &LLVMContext,
        cctx: &mut ConversionContext,
    ) -> Result<LLVMValue> {
        let op = self.get_operation().deref(ctx);
        let base = convert_value_operand(cctx, ctx, &op.get_operand(0))?;
        let indices = self.indices(ctx);
        if indices.len() != 1 {
            return input_err!(op.loc(), ToLLVMErr::InsertExtractValueIndices);
        }
        let extract_op = llvm_build_extract_value(
            &cctx.builder,
            base,
            indices[0],
            &self.get_result(ctx).unique_name(ctx),
        );
        Ok(extract_op)
    }
}

#[op_interface_impl]
impl ToLLVMValue for SelectOp {
    fn convert(
        &self,
        ctx: &Context,
        _llvm_ctx: &LLVMContext,
        cctx: &mut ConversionContext,
    ) -> Result<LLVMValue> {
        let op = self.get_operation().deref(ctx);
        let cond = convert_value_operand(cctx, ctx, &op.get_operand(0))?;
        let true_val = convert_value_operand(cctx, ctx, &op.get_operand(1))?;
        let false_val = convert_value_operand(cctx, ctx, &op.get_operand(2))?;
        let select_op = llvm_build_select(
            &cctx.builder,
            cond,
            true_val,
            false_val,
            &self.get_result(ctx).unique_name(ctx),
        );
        Ok(select_op)
    }
}

/// Conver a pliron [BasicBlock] to [LLVMBasicBlock].
fn convert_block(
    ctx: &Context,
    llvm_ctx: &LLVMContext,
    cctx: &mut ConversionContext,
    block: Ptr<BasicBlock>,
) -> Result<()> {
    let block_llvm = cctx.block_map[&block];
    llvm_position_builder_at_end(&cctx.builder, block_llvm);

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
        let op_iw = op_conv.convert(ctx, llvm_ctx, cctx)?;
        let op_ref = &*op.get_operation().deref(ctx);
        // LLVM instructions have at most one result.
        if op_ref.get_num_results() == 1 {
            cctx.value_map.insert(op_ref.get_result(0), op_iw);
        }
    }

    Ok(())
}

/// Convert a pliron [FuncOp] to [LLVMValue]
fn convert_function(
    ctx: &Context,
    llvm_ctx: &LLVMContext,
    cctx: &mut ConversionContext,
    func_op: FuncOp,
) -> Result<LLVMValue> {
    cctx.clear_per_function_data();
    let func_llvm = cctx.function_map[&func_op.get_symbol_name(ctx)];

    // Map all blocks, staring with entry.
    let mut block_iter = func_op.get_region(ctx).deref(ctx).iter(ctx);
    {
        let entry = block_iter.next().expect("Missing entry block");
        assert!(entry == func_op.get_entry_block(ctx));
        // Map entry block arguments to LLVM function arguments.
        for (arg_idx, arg) in entry.deref(ctx).arguments().enumerate() {
            cctx.value_map
                .insert(arg, llvm_get_param(func_llvm, arg_idx.try_into().unwrap()));
        }
        let llvm_entry_block = llvm_append_basic_block_in_context(
            llvm_ctx,
            func_llvm,
            &entry.deref(ctx).unique_name(ctx),
        );
        cctx.block_map.insert(entry, llvm_entry_block);
    }
    for block in block_iter {
        let llvm_block = llvm_append_basic_block_in_context(
            llvm_ctx,
            func_llvm,
            &block.deref(ctx).unique_name(ctx),
        );
        llvm_position_builder_at_end(&cctx.builder, llvm_block);
        for arg in block.deref(ctx).arguments() {
            let arg_type = convert_type(ctx, llvm_ctx, arg.get_type(ctx))?;
            let phi = llvm_build_phi(&cctx.builder, arg_type, &arg.unique_name(ctx));
            cctx.value_map.insert(arg, phi);
        }
        cctx.block_map.insert(block, llvm_block);
    }

    // Convert within every block.
    for block in topological_order(ctx, func_op.get_region(ctx)) {
        convert_block(ctx, llvm_ctx, cctx, block)?;
    }

    Ok(func_llvm)
}

#[op_interface]
trait ToLLVMConstValue {
    /// Convert from pliron [Op] to a constant [LLVMValue].
    fn convert(
        &self,
        ctx: &Context,
        llvm_ctx: &LLVMContext,
        cctx: &mut ConversionContext,
    ) -> Result<LLVMValue>;

    fn verify(_op: &dyn Op, _ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        Ok(())
    }
}

#[op_interface_impl]
impl ToLLVMConstValue for ConstantOp {
    fn convert(
        &self,
        ctx: &Context,
        llvm_ctx: &LLVMContext,
        _cctx: &mut ConversionContext,
    ) -> Result<LLVMValue> {
        let op = self.get_operation().deref(ctx);
        let value = self.get_value(ctx);
        if let Some(int_val) = value.downcast_ref::<IntegerAttr>() {
            let int_ty = int_val.get_type();
            let int_ty_llvm = convert_type(ctx, llvm_ctx, int_ty.into())?;
            let ap_int_val: APInt = int_val.clone().into();
            let const_val = llvm_const_int(int_ty_llvm, ap_int_val.to_u64(), false);
            Ok(const_val)
        // } else if let Some(_float_val) = value.downcast_ref::<FloatAttr>() {
        //     todo!()
        } else {
            input_err!(op.loc(), ToLLVMErr::ConstOpNotIntOrFloat)
        }
    }
}

#[op_interface_impl]
impl ToLLVMConstValue for UndefOp {
    fn convert(
        &self,
        ctx: &Context,
        llvm_ctx: &LLVMContext,
        _cctx: &mut ConversionContext,
    ) -> Result<LLVMValue> {
        let ty = convert_type(ctx, llvm_ctx, self.result_type(ctx))?;
        Ok(llvm_get_undef(ty))
    }
}

#[op_interface_impl]
impl ToLLVMConstValue for ZeroOp {
    fn convert(
        &self,
        ctx: &Context,
        llvm_ctx: &LLVMContext,
        _cctx: &mut ConversionContext,
    ) -> Result<LLVMValue> {
        let ty = convert_type(ctx, llvm_ctx, self.result_type(ctx))?;
        let zero_val = llvm_const_null(ty);
        Ok(zero_val)
    }
}

#[op_interface_impl]
impl ToLLVMConstValue for AddressOfOp {
    fn convert(
        &self,
        ctx: &Context,
        _llvm_ctx: &LLVMContext,
        cctx: &mut ConversionContext,
    ) -> Result<LLVMValue> {
        let sym = self.get_global_name(ctx);
        cctx.globals_map
            .get(&sym)
            .or_else(|| cctx.function_map.get(&sym))
            .cloned()
            .ok_or_else(|| input_error_noloc!(ToLLVMErr::CannotEvaluateToConst))
    }
}
#[op_interface_impl]
impl ToLLVMConstValue for InsertValueOp {
    fn convert(
        &self,
        ctx: &Context,
        llvm_ctx: &LLVMContext,
        cctx: &mut ConversionContext,
    ) -> Result<LLVMValue> {
        let op = self.get_operation().deref(ctx);
        let base = convert_to_llvm_const(ctx, cctx, llvm_ctx, op.get_operand(0))?;
        let value = convert_to_llvm_const(ctx, cctx, llvm_ctx, op.get_operand(1))?;
        let indices = self.indices(ctx);
        if indices.len() != 1 {
            return input_err!(op.loc(), ToLLVMErr::InsertExtractValueIndices);
        }

        // LLVM's builder tries to fold this, so we rely on that.
        let insert_op = llvm_build_insert_value(
            &cctx.scratch_builder,
            base,
            value,
            indices[0],
            &self.get_result(ctx).unique_name(ctx),
        );
        if !llvm_is_a::constant(insert_op) {
            return input_err!(op.loc(), ToLLVMErr::CannotEvaluateToConst);
        }
        Ok(insert_op)
    }
}

fn convert_to_llvm_const(
    ctx: &Context,
    cctx: &mut ConversionContext,
    llvm_ctx: &LLVMContext,
    value: Value,
) -> Result<LLVMValue> {
    match value {
        Value::OpResult { op, res_idx: _ } => {
            let op = Operation::get_op(op, ctx);
            if let Some(const_trans) = op_cast::<dyn ToLLVMConstValue>(&*op) {
                const_trans.convert(ctx, llvm_ctx, cctx)
            } else {
                input_err!(value.loc(ctx), ToLLVMErr::CannotEvaluateToConst)
            }
        }
        Value::BlockArgument { .. } => {
            input_err!(value.loc(ctx), ToLLVMErr::CannotEvaluateToConst)
        }
    }
}

fn convert_global_initializer(
    ctx: &Context,
    llvm_ctx: &LLVMContext,
    cctx: &mut ConversionContext,
    global_op: &GlobalOp,
) -> Result<Option<LLVMValue>> {
    if let Some(_initializer) = global_op.get_initializer_value(ctx) {
        todo!()
    }

    if let Some(init_block) = global_op.get_initializer_block(ctx) {
        let ret = Operation::get_op(init_block.deref(ctx).get_terminator(ctx).unwrap(), ctx);
        let ret = *ret.downcast::<ReturnOp>().map_err(|_| {
            input_error!(
                global_op.loc(ctx),
                ToLLVMErr::GlobalOpInitializerRegionBadReturn
            )
        })?;
        let Some(ret_val) = ret.retval(ctx) else {
            return input_err!(
                global_op.loc(ctx),
                ToLLVMErr::GlobalOpInitializerRegionBadReturn
            );
        };
        let initializer_val = convert_to_llvm_const(ctx, cctx, llvm_ctx, ret_val)?;
        return Ok(Some(initializer_val));
    }

    Ok(None)
}

/// Convert pliron [ModuleOp] to [LLVMModule].
pub fn convert_module(
    ctx: &Context,
    llvm_ctx: &LLVMContext,
    module: ModuleOp,
) -> Result<LLVMModule> {
    let mod_name = module.get_symbol_name(ctx);
    let llvm_module = LLVMModule::new(&mod_name, llvm_ctx);
    let cctx = &mut ConversionContext::new(llvm_ctx);

    // Setup the scratch builder for evaluating constants.
    let scratch_function = {
        let scratch_function = llvm_add_function(
            &llvm_module,
            "scratch",
            llvm_function_type(llvm_void_type_in_context(llvm_ctx), &[], false),
        );
        let scratch_function_entry =
            llvm_append_basic_block_in_context(llvm_ctx, scratch_function, "entry");
        llvm_position_builder_at_end(&cctx.scratch_builder, scratch_function_entry);
        scratch_function
    };

    // Create new functions and map them.
    for op in module.get_body(ctx, 0).deref(ctx).iter(ctx) {
        if let Some(func_op) = Operation::get_op(op, ctx).downcast_ref::<FuncOp>() {
            let func_ty = func_op.get_type(ctx).deref(ctx);
            let func_ty_to_llvm =
                type_cast::<dyn ToLLVMType>(&**func_ty).ok_or(input_error_noloc!(
                    ToLLVMErr::MissingOpConversion(func_ty.disp(ctx).to_string())
                ))?;
            let fn_ty_llvm = func_ty_to_llvm.convert(ctx, llvm_ctx)?;
            let func_llvm =
                llvm_add_function(&llvm_module, &func_op.get_symbol_name(ctx), fn_ty_llvm);
            cctx.function_map
                .insert(func_op.get_symbol_name(ctx), func_llvm);
        }
        if let Some(global_op) = Operation::get_op(op, ctx).downcast_ref::<GlobalOp>() {
            let global_ty = global_op.get_type(ctx);
            let global_ty_llvm = convert_type(ctx, llvm_ctx, global_ty)?;
            let global_name = global_op.get_symbol_name(ctx);
            let global_llvm = llvm_add_global(&llvm_module, global_ty_llvm, &global_name);
            cctx.globals_map.insert(global_name, global_llvm);
        }
    }

    for op in module.get_body(ctx, 0).deref(ctx).iter(ctx) {
        if let Some(func_op) = Operation::get_op(op, ctx).downcast_ref::<FuncOp>() {
            convert_function(ctx, llvm_ctx, cctx, *func_op)?;
        }
        if let Some(global_op) = Operation::get_op(op, ctx).downcast_ref::<GlobalOp>() {
            let global_name = global_op.get_symbol_name(ctx);
            let global_llvm = cctx.globals_map[&global_name];
            if let Some(initializer) = convert_global_initializer(ctx, llvm_ctx, cctx, global_op)? {
                llvm_set_initializer(global_llvm, initializer);
            }
        }
    }

    // Delete the scratch function
    llvm_delete_function(scratch_function);

    Ok(llvm_module)
}
