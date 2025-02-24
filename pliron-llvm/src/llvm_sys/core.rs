//! Safe wrappers around llvm_sys::core.

use std::{
    mem::{MaybeUninit, forget},
    ptr,
};

use llvm_sys::{
    LLVMIntPredicate, LLVMOpcode, LLVMTypeKind, LLVMValueKind,
    analysis::LLVMVerifyModule,
    bit_writer::LLVMWriteBitcodeToFile,
    core::{
        LLVMAddFunction, LLVMAddIncoming, LLVMAppendBasicBlockInContext, LLVMArrayType2,
        LLVMBasicBlockAsValue, LLVMBuildAdd, LLVMBuildAnd, LLVMBuildArrayAlloca, LLVMBuildBitCast,
        LLVMBuildBr, LLVMBuildCall2, LLVMBuildCondBr, LLVMBuildExtractValue, LLVMBuildGEP2,
        LLVMBuildICmp, LLVMBuildInsertValue, LLVMBuildLoad2, LLVMBuildMul, LLVMBuildOr,
        LLVMBuildPhi, LLVMBuildRet, LLVMBuildRetVoid, LLVMBuildSDiv, LLVMBuildSExt, LLVMBuildSRem,
        LLVMBuildShl, LLVMBuildStore, LLVMBuildSub, LLVMBuildUDiv, LLVMBuildURem, LLVMBuildXor,
        LLVMBuildZExt, LLVMClearInsertionPosition, LLVMConstInt, LLVMConstIntGetZExtValue,
        LLVMContextCreate, LLVMContextDispose, LLVMCountIncoming, LLVMCountParamTypes,
        LLVMCountParams, LLVMCountStructElementTypes, LLVMCreateBuilderInContext,
        LLVMCreateMemoryBufferWithContentsOfFile, LLVMDisposeMemoryBuffer, LLVMDisposeMessage,
        LLVMDisposeModule, LLVMDumpModule, LLVMDumpType, LLVMDumpValue, LLVMFunctionType,
        LLVMGetAllocatedType, LLVMGetArrayLength2, LLVMGetBasicBlockName,
        LLVMGetBasicBlockTerminator, LLVMGetCalledFunctionType, LLVMGetCalledValue,
        LLVMGetConstOpcode, LLVMGetElementType, LLVMGetFirstBasicBlock, LLVMGetFirstFunction,
        LLVMGetFirstInstruction, LLVMGetFirstParam, LLVMGetGEPSourceElementType,
        LLVMGetICmpPredicate, LLVMGetIncomingBlock, LLVMGetIncomingValue, LLVMGetIndices,
        LLVMGetInsertBlock, LLVMGetInstructionOpcode, LLVMGetInstructionParent,
        LLVMGetIntTypeWidth, LLVMGetModuleIdentifier, LLVMGetNSW, LLVMGetNUW,
        LLVMGetNextBasicBlock, LLVMGetNextFunction, LLVMGetNextInstruction, LLVMGetNextParam,
        LLVMGetNumArgOperands, LLVMGetNumIndices, LLVMGetNumOperands, LLVMGetOperand, LLVMGetParam,
        LLVMGetParamTypes, LLVMGetPreviousBasicBlock, LLVMGetPreviousFunction,
        LLVMGetPreviousInstruction, LLVMGetPreviousParam, LLVMGetReturnType,
        LLVMGetStructElementTypes, LLVMGetStructName, LLVMGetTypeKind, LLVMGetUndef,
        LLVMGetValueKind, LLVMGetValueName2, LLVMGlobalGetValueType, LLVMIntTypeInContext,
        LLVMIsAFunction, LLVMIsATerminatorInst, LLVMIsAUser, LLVMIsOpaqueStruct,
        LLVMModuleCreateWithNameInContext, LLVMPointerTypeInContext, LLVMPositionBuilderAtEnd,
        LLVMPositionBuilderBefore, LLVMPrintModuleToFile, LLVMStructCreateNamed, LLVMStructSetBody,
        LLVMStructTypeInContext, LLVMTypeIsSized, LLVMTypeOf, LLVMValueAsBasicBlock,
        LLVMValueIsBasicBlock, LLVMVoidTypeInContext,
    },
    ir_reader::LLVMParseIRInContext,
    prelude::{
        LLVMBasicBlockRef, LLVMBuilderRef, LLVMContextRef, LLVMMemoryBufferRef, LLVMModuleRef,
        LLVMTypeRef, LLVMValueRef,
    },
};

use crate::llvm_sys::{ToBool, c_array_to_vec, cstr_to_string, uninitialized_vec};

use super::{sized_cstr_to_string, to_c_str};

/// Opaque wrapper around LLVMValueRef to hide the raw pointer
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct LLVMValue(LLVMValueRef);

impl From<LLVMValueRef> for LLVMValue {
    fn from(value: LLVMValueRef) -> Self {
        LLVMValue(value)
    }
}

impl From<LLVMValue> for LLVMValueRef {
    fn from(value: LLVMValue) -> Self {
        value.0
    }
}

/// Opaque wrapper around LLVMTypeRef to hide the raw pointer
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct LLVMType(LLVMTypeRef);

impl From<LLVMTypeRef> for LLVMType {
    fn from(ty: LLVMTypeRef) -> Self {
        LLVMType(ty)
    }
}

impl From<LLVMType> for LLVMTypeRef {
    fn from(ty: LLVMType) -> Self {
        ty.0
    }
}

/// Managed LLVMContext
pub struct LLVMContext(LLVMContextRef);

impl Default for LLVMContext {
    fn default() -> Self {
        unsafe { LLVMContext(LLVMContextCreate()) }
    }
}

impl Drop for LLVMContext {
    fn drop(&mut self) {
        unsafe { LLVMContextDispose(self.0) }
    }
}

/// Opaque wrapper around LLVMBasicBlockRef to hide the raw pointer
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct LLVMBasicBlock(LLVMBasicBlockRef);

impl From<LLVMBasicBlockRef> for LLVMBasicBlock {
    fn from(ty: LLVMBasicBlockRef) -> Self {
        LLVMBasicBlock(ty)
    }
}

impl From<LLVMBasicBlock> for LLVMBasicBlockRef {
    fn from(ty: LLVMBasicBlock) -> Self {
        ty.0
    }
}

/// Managed LLVMBuilder.
pub struct LLVMBuilder(LLVMBuilderRef);

impl LLVMBuilder {
    pub fn new(context: &LLVMContext) -> Self {
        unsafe { LLVMBuilder(LLVMCreateBuilderInContext(context.0)) }
    }
}

/// LLVMGetValueName2
pub fn llvm_get_value_name(val: LLVMValue) -> Option<String> {
    let mut len = 0;
    let buf_ptr = unsafe { LLVMGetValueName2(val.into(), &mut len) };
    if buf_ptr.is_null() {
        return None;
    }
    sized_cstr_to_string(buf_ptr, len)
}

/// LLVMGetModuleIdentifier
pub fn llvm_get_module_identifier(module: &LLVMModule) -> Option<String> {
    let mut len = 0;
    let buf_ptr = unsafe { LLVMGetModuleIdentifier(module.0, &mut len) };
    if buf_ptr.is_null() {
        return None;
    }
    sized_cstr_to_string(buf_ptr, len)
}

/// LLVMDumpValue
pub fn llvm_dump_value(val: LLVMValue) {
    unsafe { LLVMDumpValue(val.into()) }
}

/// LLVMDumpType
pub fn llvm_dump_type(ty: LLVMType) {
    unsafe { LLVMDumpType(ty.into()) }
}

/// LLVMDumpModule
pub fn llvm_dump_module(module: &LLVMModule) {
    unsafe { LLVMDumpModule(module.0) }
}

/// The family of LLVMIsA* functions for Value
pub mod llvm_is_a {
    use llvm_sys::core::{
        LLVMIsAAllocaInst, LLVMIsAArgument, LLVMIsACallInst, LLVMIsAConstantExpr,
        LLVMIsAConstantInt, LLVMIsAExtractValueInst, LLVMIsAGetElementPtrInst, LLVMIsAGlobalValue,
        LLVMIsAICmpInst, LLVMIsAInsertValueInst, LLVMIsAInstruction, LLVMIsAInvokeInst,
        LLVMIsAPHINode,
    };

    use super::*;

    /// LLVMIsAFunction
    pub fn function(val: LLVMValue) -> bool {
        unsafe { !LLVMIsAFunction(val.into()).is_null() }
    }

    /// LLVMIsAUser
    pub fn user(val: LLVMValue) -> bool {
        unsafe { !LLVMIsAUser(val.into()).is_null() }
    }

    /// LLVMIsAInstruction
    pub fn instruction(val: LLVMValue) -> bool {
        unsafe { !LLVMIsAInstruction(val.into()).is_null() }
    }

    /// LLVMIsAConstantInt
    pub fn constant_int(val: LLVMValue) -> bool {
        unsafe { !LLVMIsAConstantInt(val.into()).is_null() }
    }

    /// LLVMIsAConstantExpr
    pub fn constant_expr(val: LLVMValue) -> bool {
        unsafe { !LLVMIsAConstantExpr(val.into()).is_null() }
    }

    /// LLVMIsAPHINode
    pub fn phi_node(val: LLVMValue) -> bool {
        unsafe { !LLVMIsAPHINode(val.into()).is_null() }
    }

    /// LLVMIsAAllocaInst
    pub fn alloca_inst(val: LLVMValue) -> bool {
        unsafe { !LLVMIsAAllocaInst(val.into()).is_null() }
    }

    /// LLVMIsAICmpInst
    pub fn icmp_inst(val: LLVMValue) -> bool {
        unsafe { !LLVMIsAICmpInst(val.into()).is_null() }
    }

    /// LLVMIsAArgument
    pub fn argument(val: LLVMValue) -> bool {
        unsafe { !LLVMIsAArgument(val.into()).is_null() }
    }

    /// LLVMIsAGlobalValue
    pub fn global_value(val: LLVMValue) -> bool {
        unsafe { !LLVMIsAGlobalValue(val.into()).is_null() }
    }

    /// LLVMIsACallInst
    pub fn call_inst(val: LLVMValue) -> bool {
        unsafe { !LLVMIsACallInst(val.into()).is_null() }
    }

    /// LLVMIsAInvokeInst
    pub fn invoke_inst(val: LLVMValue) -> bool {
        unsafe { !LLVMIsAInvokeInst(val.into()).is_null() }
    }

    /// LLVMIsAGetElementPtrInst
    pub fn get_element_ptr_inst(val: LLVMValue) -> bool {
        unsafe { !LLVMIsAGetElementPtrInst(val.into()).is_null() }
    }

    /// LLVMIsAInsertValueInst
    pub fn insert_value_inst(val: LLVMValue) -> bool {
        unsafe { !LLVMIsAInsertValueInst(val.into()).is_null() }
    }

    /// LLVMIsAExtractValueInst
    pub fn extract_value_inst(val: LLVMValue) -> bool {
        unsafe { !LLVMIsAExtractValueInst(val.into()).is_null() }
    }
}

/// LLVMTypeOf
pub fn llvm_type_of(val: LLVMValue) -> LLVMType {
    unsafe { LLVMTypeOf(val.into()).into() }
}

/// LLVMGlobalGetValueType
pub fn llvm_global_get_value_type(val: LLVMValue) -> LLVMType {
    assert!(llvm_is_a::global_value(val));
    unsafe { LLVMGlobalGetValueType(val.into()).into() }
}

/// LLVMTypeIsSized
pub fn llvm_type_is_sized(ty: LLVMType) -> bool {
    unsafe { LLVMTypeIsSized(ty.into()).to_bool() }
}

/// Type.h: isAggregateType()
pub fn llvm_is_aggregate_type(ty: LLVMType) -> bool {
    matches!(
        llvm_get_type_kind(ty),
        LLVMTypeKind::LLVMArrayTypeKind | LLVMTypeKind::LLVMStructTypeKind
    )
}

/// LLVMGetTypeKind
pub fn llvm_get_type_kind(ty: LLVMType) -> LLVMTypeKind {
    unsafe { LLVMGetTypeKind(ty.into()) }
}

/// LLVMGetElementType
pub fn llvm_get_element_type(ty: LLVMType) -> LLVMType {
    assert!(matches!(
        llvm_get_type_kind(ty),
        LLVMTypeKind::LLVMArrayTypeKind | LLVMTypeKind::LLVMVectorTypeKind
    ));
    unsafe { LLVMGetElementType(ty.into()).into() }
}

/// LLVMGetArrayLength2
pub fn llvm_get_array_length2(ty: LLVMType) -> u64 {
    assert!(llvm_get_type_kind(ty) == LLVMTypeKind::LLVMArrayTypeKind);
    unsafe { LLVMGetArrayLength2(ty.into()) }
}

/// LLVMGetReturnType
pub fn llvm_get_return_type(ty: LLVMType) -> LLVMType {
    assert!(llvm_get_type_kind(ty) == LLVMTypeKind::LLVMFunctionTypeKind);
    unsafe { LLVMGetReturnType(ty.into()).into() }
}

/// LLVMCountParamTypes
pub fn llvm_count_param_types(ty: LLVMType) -> u32 {
    assert!(llvm_get_type_kind(ty) == LLVMTypeKind::LLVMFunctionTypeKind);
    unsafe { LLVMCountParamTypes(ty.into()) }
}

/// LLVMGetParamTypes
pub fn llvm_get_param_types(ty: LLVMType) -> Vec<LLVMType> {
    let params_count = llvm_count_param_types(ty) as usize;
    unsafe {
        let mut buffer = uninitialized_vec::<LLVMTypeRef>(params_count);
        LLVMGetParamTypes(ty.into(), (*buffer.as_mut_ptr()).as_mut_ptr());
        buffer.assume_init()
    }
    .into_iter()
    .map(Into::into)
    .collect()
}

/// LLVMGetIntTypeWidth
pub fn llvm_get_int_type_width(ty: LLVMType) -> u32 {
    assert!(llvm_get_type_kind(ty) == LLVMTypeKind::LLVMIntegerTypeKind);
    unsafe { LLVMGetIntTypeWidth(ty.into()) }
}

/// LLVMIsOpaqueStruct
pub fn llvm_is_opaque_struct(ty: LLVMType) -> bool {
    assert!(llvm_get_type_kind(ty) == LLVMTypeKind::LLVMStructTypeKind);
    unsafe { LLVMIsOpaqueStruct(ty.into()) }.to_bool()
}

/// LLVMCountStructElementTypes
pub fn llvm_count_struct_element_types(ty: LLVMType) -> u32 {
    assert!(llvm_get_type_kind(ty) == LLVMTypeKind::LLVMStructTypeKind);
    unsafe { LLVMCountStructElementTypes(ty.into()) }
}

/// LLVMGetStructElementTypes
pub fn llvm_get_struct_element_types(ty: LLVMType) -> Vec<LLVMType> {
    let element_types_count = llvm_count_struct_element_types(ty) as usize;
    unsafe {
        let mut buffer = uninitialized_vec::<LLVMTypeRef>(element_types_count);
        LLVMGetStructElementTypes(ty.into(), (*buffer.as_mut_ptr()).as_mut_ptr());
        buffer.assume_init()
    }
    .into_iter()
    .map(Into::into)
    .collect()
}

/// LLVMGetStructName
pub fn llvm_get_struct_name(ty: LLVMType) -> Option<String> {
    assert!(llvm_get_type_kind(ty) == LLVMTypeKind::LLVMStructTypeKind);
    cstr_to_string(unsafe { LLVMGetStructName(ty.into()) })
}

/// LLVMIsATerminatorInst
pub fn llvm_is_a_terminator_inst(val: LLVMValue) -> bool {
    !unsafe { LLVMIsATerminatorInst(val.into()) }.is_null()
}

/// LLVMGetBasicBlockTerminator
pub fn llvm_get_basic_block_terminator(bb: LLVMBasicBlock) -> Option<LLVMValue> {
    let bbref = unsafe { LLVMGetBasicBlockTerminator(bb.into()) };
    (!bbref.is_null()).then_some(bbref.into())
}

// LLVMGetValueKind
pub fn llvm_get_value_kind(val: LLVMValue) -> LLVMValueKind {
    unsafe { LLVMGetValueKind(val.into()) }
}

/// LLVMGetInstructionOpcode
pub fn llvm_get_instruction_opcode(val: LLVMValue) -> LLVMOpcode {
    assert!(llvm_get_value_kind(val) == LLVMValueKind::LLVMInstructionValueKind);
    unsafe { LLVMGetInstructionOpcode(val.into()) }
}

/// LLVMGetConstOpcode
pub fn llvm_get_const_opcode(val: LLVMValue) -> LLVMOpcode {
    assert!(llvm_is_a::constant_expr(val));
    unsafe { LLVMGetConstOpcode(val.into()) }
}

/// LLVMGetInstructionParent
pub fn llvm_get_instruction_parent(inst: LLVMValue) -> Option<LLVMBasicBlock> {
    assert!(llvm_is_a::instruction(inst));
    unsafe {
        let parent = LLVMGetInstructionParent(inst.into());
        (!parent.is_null()).then_some(parent.into())
    }
}

/// LLVMGetNumOperands
pub fn llvm_get_num_operands(val: LLVMValue) -> u32 {
    assert!(llvm_is_a::user(val));
    unsafe { LLVMGetNumOperands(val.into()) as u32 }
}

/// LLVMGetOperand
pub fn llvm_get_operand(val: LLVMValue, index: u32) -> LLVMValue {
    assert!(index < llvm_get_num_operands(val));
    unsafe { LLVMGetOperand(val.into(), index).into() }
}

/// LLVMBasicBlockAsValue
pub fn llvm_basic_block_as_value(block: LLVMBasicBlock) -> LLVMValue {
    unsafe { LLVMBasicBlockAsValue(block.into()).into() }
}

/// LLVMValueIsBasicBlock
pub fn llvm_value_is_basic_block(val: LLVMValue) -> bool {
    unsafe { LLVMValueIsBasicBlock(val.into()).to_bool() }
}

/// LLVMValueAsBasicBlock
pub fn llvm_value_as_basic_block(val: LLVMValue) -> LLVMBasicBlock {
    assert!(llvm_value_is_basic_block(val));
    unsafe { LLVMValueAsBasicBlock(val.into()).into() }
}

/// LLVMGetBasicBlockName
pub fn llvm_get_basic_block_name(block: LLVMBasicBlock) -> Option<String> {
    cstr_to_string(unsafe { LLVMGetBasicBlockName(block.into()) })
}

/// LLVMGetFirstBasicBlock
pub fn llvm_get_first_basic_block(fn_val: LLVMValue) -> Option<LLVMBasicBlock> {
    assert!(llvm_is_a::function(fn_val));
    unsafe {
        let first_block = LLVMGetFirstBasicBlock(fn_val.into());
        (!first_block.is_null()).then_some(first_block.into())
    }
}

/// LLVMGetNextBasicBlock
pub fn llvm_get_next_basic_block(bb: LLVMBasicBlock) -> Option<LLVMBasicBlock> {
    unsafe {
        let next_block = LLVMGetNextBasicBlock(bb.into());
        (!next_block.is_null()).then_some(next_block.into())
    }
}

/// LLVMGetPreviousBasicBlock
pub fn llvm_get_previous_basic_block(bb: LLVMBasicBlock) -> Option<LLVMBasicBlock> {
    unsafe {
        let prev_block = LLVMGetPreviousBasicBlock(bb.into());
        (!prev_block.is_null()).then_some(prev_block.into())
    }
}

/// Iterate over all `BasicBlock`s in a function.
pub struct BasicBlockIter(pub Option<LLVMBasicBlock>);

impl Iterator for BasicBlockIter {
    type Item = LLVMBasicBlock;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(bb) = self.0 {
            self.0 = llvm_get_next_basic_block(bb);
            Some(bb)
        } else {
            None
        }
    }
}

/// Get an iterator over the basic blocks of a function.
pub fn basic_block_iter(fn_val: LLVMValue) -> BasicBlockIter {
    BasicBlockIter(llvm_get_first_basic_block(fn_val))
}

/// LLVMGetFirstInstruction
pub fn llvm_get_first_instruction(bb: LLVMBasicBlock) -> Option<LLVMValue> {
    unsafe {
        let first_instr = LLVMGetFirstInstruction(bb.into());
        (!first_instr.is_null()).then_some(first_instr.into())
    }
}

/// LLVMGetNextInstruction
pub fn llvm_get_next_instruction(instr: LLVMValue) -> Option<LLVMValue> {
    assert!(llvm_is_a::instruction(instr));
    unsafe {
        let next_instr = LLVMGetNextInstruction(instr.into());
        (!next_instr.is_null()).then_some(next_instr.into())
    }
}

/// LLVMGetPreviousInstruction
pub fn llvm_get_previous_instruction(instr: LLVMValue) -> Option<LLVMValue> {
    assert!(llvm_is_a::instruction(instr));
    unsafe {
        let prev_instr = LLVMGetPreviousInstruction(instr.into());
        (!prev_instr.is_null()).then_some(prev_instr.into())
    }
}

/// Iterate over all `Instruction`s in a basic block.
pub struct InstructionIter(pub Option<LLVMValue>);

impl Iterator for InstructionIter {
    type Item = LLVMValue;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(instr) = self.0 {
            self.0 = llvm_get_next_instruction(instr);
            Some(instr)
        } else {
            None
        }
    }
}

/// Get an iterator over the instructions of a basic block.
pub fn instruction_iter(bb: LLVMBasicBlock) -> InstructionIter {
    InstructionIter(llvm_get_first_instruction(bb))
}

/// LLVMCountIncoming
pub fn llvm_count_incoming(phi_node: LLVMValue) -> u32 {
    assert!(llvm_is_a::phi_node(phi_node));
    unsafe { LLVMCountIncoming(phi_node.into()) }
}

/// LLVMGetIncomingValue
pub fn llvm_get_incoming_value(phi_node: LLVMValue, index: u32) -> LLVMValue {
    assert!(index < llvm_count_incoming(phi_node));
    unsafe { LLVMGetIncomingValue(phi_node.into(), index).into() }
}

/// LLVMGetIncomingBlock
pub fn llvm_get_incoming_block(phi_node: LLVMValue, index: u32) -> LLVMBasicBlock {
    assert!(index < llvm_count_incoming(phi_node));
    unsafe { LLVMGetIncomingBlock(phi_node.into(), index).into() }
}

/// Iterate over all the incoming edges of a phi value.
pub struct IncomingIter {
    phi_node: LLVMValue,
    i: u32,
    count: u32,
}

impl Iterator for IncomingIter {
    type Item = (LLVMValue, LLVMBasicBlock);

    fn next(&mut self) -> Option<Self::Item> {
        if self.i < self.count {
            let result = (
                llvm_get_incoming_value(self.phi_node, self.i),
                llvm_get_incoming_block(self.phi_node, self.i),
            );
            self.i += 1;
            Some(result)
        } else {
            None
        }
    }
}

/// Get an incoming edge iterator.
pub fn incoming_iter(phi_node: LLVMValue) -> IncomingIter {
    IncomingIter {
        phi_node,
        i: 0,
        count: llvm_count_incoming(phi_node),
    }
}

/// LLVMConstIntGetZExtValue
pub fn llvm_const_int_get_zext_value(val: LLVMValue) -> u64 {
    assert!(llvm_is_a::constant_int(val));
    unsafe { LLVMConstIntGetZExtValue(val.into()) }
}

/// LLVMGetAllocatedType
pub fn llvm_get_allocated_type(val: LLVMValue) -> LLVMType {
    assert!(llvm_is_a::alloca_inst(val));
    unsafe { LLVMGetAllocatedType(val.into()).into() }
}

/// LLVMGetICmpPredicate
pub fn llvm_get_icmp_predicate(val: LLVMValue) -> LLVMIntPredicate {
    assert!(llvm_is_a::icmp_inst(val) || llvm_get_const_opcode(val) == LLVMOpcode::LLVMICmp);
    unsafe { LLVMGetICmpPredicate(val.into()) }
}

/// LLVMCountParams
pub fn llvm_count_params(func: LLVMValue) -> u32 {
    assert!(llvm_is_a::function(func));
    unsafe { LLVMCountParams(func.into()) }
}

/// LLVMGetFirstParam
pub fn llvm_get_first_param(func: LLVMValue) -> Option<LLVMValue> {
    assert!(llvm_is_a::function(func));
    unsafe {
        let first_param = LLVMGetFirstParam(func.into());
        (!first_param.is_null()).then_some(first_param.into())
    }
}

/// LLVMGetNextParam
pub fn llvm_get_next_param(val: LLVMValue) -> Option<LLVMValue> {
    assert!(llvm_is_a::argument(val));
    unsafe {
        let next_param = LLVMGetNextParam(val.into());
        (!next_param.is_null()).then_some(next_param.into())
    }
}

/// LLVMGetPreviousParam
pub fn llvm_get_previous_param(val: LLVMValue) -> Option<LLVMValue> {
    assert!(llvm_is_a::argument(val));
    unsafe {
        let prev_param = LLVMGetPreviousParam(val.into());
        (!prev_param.is_null()).then_some(prev_param.into())
    }
}

/// Iterate over all `Parameters`s of a `Function`.
pub struct ParamIter(pub Option<LLVMValue>);

impl Iterator for ParamIter {
    type Item = LLVMValue;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(param) = self.0 {
            self.0 = llvm_get_next_param(param);
            Some(param)
        } else {
            None
        }
    }
}

/// Get an iterator over the parameters of a function.
pub fn param_iter(func: LLVMValue) -> ParamIter {
    assert!(llvm_is_a::function(func));
    ParamIter(llvm_get_first_param(func))
}

/// LLVMGetParam
pub fn llvm_get_param(func: LLVMValue, idx: u32) -> LLVMValue {
    assert!(idx < llvm_count_params(func));
    unsafe { LLVMGetParam(func.into(), idx).into() }
}

/// LLVMGetFirstFunction
pub fn llvm_get_first_function(module: &LLVMModule) -> Option<LLVMValue> {
    unsafe {
        let first_func = LLVMGetFirstFunction(module.0);
        (!first_func.is_null()).then_some(first_func.into())
    }
}

/// LLVMGetNextFunction
pub fn llvm_get_next_function(func: LLVMValue) -> Option<LLVMValue> {
    assert!(llvm_is_a::function(func));
    unsafe {
        let next_func = LLVMGetNextFunction(func.into());
        (!next_func.is_null()).then_some(next_func.into())
    }
}

/// LLVMGetPreviousFunction
pub fn llvm_get_previous_function(func: LLVMValue) -> Option<LLVMValue> {
    assert!(llvm_is_a::function(func));
    unsafe {
        let prev_func = LLVMGetPreviousFunction(func.into());
        (!prev_func.is_null()).then_some(prev_func.into())
    }
}

/// Iterate over all `Function`s in a `Module`.
pub struct FunctionIter(pub Option<LLVMValue>);

impl Iterator for FunctionIter {
    type Item = LLVMValue;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(param) = self.0 {
            self.0 = llvm_get_next_function(param);
            Some(param)
        } else {
            None
        }
    }
}

/// Get an iterator over the functions of a module.
pub fn function_iter(module: &LLVMModule) -> FunctionIter {
    FunctionIter(llvm_get_first_function(module))
}

/// LLVMGetInsertBlock
pub fn llvm_get_insert_block(builder: &LLVMBuilder) -> Option<LLVMBasicBlock> {
    unsafe {
        let insert_block = LLVMGetInsertBlock(builder.0);
        (!insert_block.is_null()).then_some(insert_block.into())
    }
}

/// LLVMClearInsertionPosition
pub fn llvm_clear_insertion_position(builder: &LLVMBuilder) {
    unsafe { LLVMClearInsertionPosition(builder.0) }
}

/// LLVMPositionBuilderAtEnd
pub fn llvm_position_builder_at_end(builder: &LLVMBuilder, block: LLVMBasicBlock) {
    unsafe { LLVMPositionBuilderAtEnd(builder.0, block.into()) }
}

/// LLVMPositionBuilderBefore
pub fn llvm_position_builder_before(builder: &LLVMBuilder, inst: LLVMValue) {
    assert!(llvm_is_a::instruction(inst));
    unsafe { LLVMPositionBuilderBefore(builder.0, inst.into()) }
}

/// LLVMIntTypeInContext
pub fn llvm_int_type_in_context(context: &LLVMContext, width: u32) -> LLVMType {
    unsafe { LLVMIntTypeInContext(context.0, width).into() }
}

/// ArrayType::isValidElementType
pub fn llvm_is_valid_array_element_type(ty: LLVMType) -> bool {
    !matches!(
        llvm_get_type_kind(ty),
        LLVMTypeKind::LLVMVoidTypeKind
            | LLVMTypeKind::LLVMLabelTypeKind
            | LLVMTypeKind::LLVMMetadataTypeKind
            | LLVMTypeKind::LLVMFunctionTypeKind
            | LLVMTypeKind::LLVMTokenTypeKind
            | LLVMTypeKind::LLVMX86_AMXTypeKind
    )
}

/// LLVMArrayType2
pub fn llvm_array_type2(elem_ty: LLVMType, element_count: u64) -> LLVMType {
    assert!(llvm_is_valid_array_element_type(elem_ty));
    unsafe { LLVMArrayType2(elem_ty.into(), element_count).into() }
}

/// isFirstClassType
pub fn llvm_is_first_class_type(ty: LLVMType) -> bool {
    !matches!(
        llvm_get_type_kind(ty),
        LLVMTypeKind::LLVMVoidTypeKind | LLVMTypeKind::LLVMFunctionTypeKind
    )
}

/// FunctionType::isValidArgumentType
pub fn llvm_is_valid_function_argument_type(arg_ty: LLVMType) -> bool {
    llvm_is_first_class_type(arg_ty)
}

/// FunctionType::isValidReturnType
pub fn llvm_is_valid_function_return_type(ret_ty: LLVMType) -> bool {
    !matches!(
        llvm_get_type_kind(ret_ty),
        LLVMTypeKind::LLVMLabelTypeKind
            | LLVMTypeKind::LLVMFunctionTypeKind
            | LLVMTypeKind::LLVMMetadataTypeKind
    )
}

/// LLVMFunctionType
pub fn llvm_function_type(ret_ty: LLVMType, param_tys: &[LLVMType], is_var_arg: bool) -> LLVMType {
    assert!(llvm_is_valid_function_return_type(ret_ty));
    assert!(
        param_tys
            .iter()
            .all(|param_ty| llvm_is_valid_function_argument_type(*param_ty))
    );
    let mut param_tys: Vec<_> = param_tys.iter().cloned().map(Into::into).collect();
    unsafe {
        LLVMFunctionType(
            ret_ty.into(),
            param_tys.as_mut_ptr(),
            param_tys.len().try_into().unwrap(),
            is_var_arg as i32,
        )
        .into()
    }
}

/// LLVMVoidTypeInContext
pub fn llvm_void_type_in_context(context: &LLVMContext) -> LLVMType {
    unsafe { LLVMVoidTypeInContext(context.0).into() }
}

/// LLVMPointerTypeInContext
pub fn llvm_pointer_type_in_context(context: &LLVMContext, addr_space: u32) -> LLVMType {
    unsafe { LLVMPointerTypeInContext(context.0, addr_space).into() }
}

/// LLVMStructCreateNamed
pub fn llvm_struct_create_named(context: &LLVMContext, name: &str) -> LLVMType {
    unsafe { LLVMStructCreateNamed(context.0, to_c_str(name).as_ptr()).into() }
}

/// StructType::isValidElementType
pub fn llvm_is_valid_struct_element_type(ty: LLVMType) -> bool {
    !matches!(
        llvm_get_type_kind(ty),
        LLVMTypeKind::LLVMVoidTypeKind
            | LLVMTypeKind::LLVMLabelTypeKind
            | LLVMTypeKind::LLVMMetadataTypeKind
            | LLVMTypeKind::LLVMFunctionTypeKind
            | LLVMTypeKind::LLVMTokenTypeKind
    )
}

/// LLVMStructTypeInContext
pub fn llvm_struct_type_in_context(
    context: &LLVMContext,
    elem_tys: &[LLVMType],
    is_packed: bool,
) -> LLVMType {
    assert!(
        elem_tys
            .iter()
            .all(|elem_ty| llvm_is_valid_struct_element_type(*elem_ty))
    );
    let mut elem_tys: Vec<_> = elem_tys.iter().cloned().map(Into::into).collect();
    unsafe {
        LLVMStructTypeInContext(
            context.0,
            elem_tys.as_mut_ptr(),
            elem_tys.len().try_into().unwrap(),
            is_packed as i32,
        )
        .into()
    }
}

/// LLVMStructSetBody
pub fn llvm_struct_set_body(struct_ty: LLVMType, elem_tys: &[LLVMType], is_packed: bool) {
    assert!(llvm_get_type_kind(struct_ty) == LLVMTypeKind::LLVMStructTypeKind);
    assert!(
        elem_tys
            .iter()
            .all(|elem_ty| llvm_is_valid_struct_element_type(*elem_ty))
    );
    let mut elem_tys: Vec<_> = elem_tys.iter().cloned().map(Into::into).collect();
    unsafe {
        LLVMStructSetBody(
            struct_ty.into(),
            elem_tys.as_mut_ptr(),
            elem_tys.len().try_into().unwrap(),
            is_packed as i32,
        )
    }
}

/// LLVMBuildAdd
pub fn llvm_build_add(
    builder: &LLVMBuilder,
    lhs: LLVMValue,
    rhs: LLVMValue,
    name: &str,
) -> LLVMValue {
    assert!(llvm_get_insert_block(builder).is_some());
    unsafe { LLVMBuildAdd(builder.0, lhs.into(), rhs.into(), to_c_str(name).as_ptr()).into() }
}

/// LLVMBuildSub
pub fn llvm_build_sub(
    builder: &LLVMBuilder,
    lhs: LLVMValue,
    rhs: LLVMValue,
    name: &str,
) -> LLVMValue {
    assert!(llvm_get_insert_block(builder).is_some());
    unsafe { LLVMBuildSub(builder.0, lhs.into(), rhs.into(), to_c_str(name).as_ptr()).into() }
}

/// LLVMBuildMul
pub fn llvm_build_mul(
    builder: &LLVMBuilder,
    lhs: LLVMValue,
    rhs: LLVMValue,
    name: &str,
) -> LLVMValue {
    assert!(llvm_get_insert_block(builder).is_some());
    unsafe { LLVMBuildMul(builder.0, lhs.into(), rhs.into(), to_c_str(name).as_ptr()).into() }
}

/// LLVMBuildSDiv
pub fn llvm_build_sdiv(
    builder: &LLVMBuilder,
    lhs: LLVMValue,
    rhs: LLVMValue,
    name: &str,
) -> LLVMValue {
    assert!(llvm_get_insert_block(builder).is_some());
    unsafe { LLVMBuildSDiv(builder.0, lhs.into(), rhs.into(), to_c_str(name).as_ptr()).into() }
}

/// LLVMBuildUDiv
pub fn llvm_build_udiv(
    builder: &LLVMBuilder,
    lhs: LLVMValue,
    rhs: LLVMValue,
    name: &str,
) -> LLVMValue {
    assert!(llvm_get_insert_block(builder).is_some());
    unsafe { LLVMBuildUDiv(builder.0, lhs.into(), rhs.into(), to_c_str(name).as_ptr()).into() }
}

/// LLVMBuildURem
pub fn llvm_build_urem(
    builder: &LLVMBuilder,
    lhs: LLVMValue,
    rhs: LLVMValue,
    name: &str,
) -> LLVMValue {
    assert!(llvm_get_insert_block(builder).is_some());
    unsafe { LLVMBuildURem(builder.0, lhs.into(), rhs.into(), to_c_str(name).as_ptr()).into() }
}

/// LLVMBuildSRem
pub fn llvm_build_srem(
    builder: &LLVMBuilder,
    lhs: LLVMValue,
    rhs: LLVMValue,
    name: &str,
) -> LLVMValue {
    assert!(llvm_get_insert_block(builder).is_some());
    unsafe { LLVMBuildSRem(builder.0, lhs.into(), rhs.into(), to_c_str(name).as_ptr()).into() }
}

/// LLVMBuildAnd
pub fn llvm_build_and(
    builder: &LLVMBuilder,
    lhs: LLVMValue,
    rhs: LLVMValue,
    name: &str,
) -> LLVMValue {
    assert!(llvm_get_insert_block(builder).is_some());
    unsafe { LLVMBuildAnd(builder.0, lhs.into(), rhs.into(), to_c_str(name).as_ptr()).into() }
}

/// LLVMBuildOr
pub fn llvm_build_or(
    builder: &LLVMBuilder,
    lhs: LLVMValue,
    rhs: LLVMValue,
    name: &str,
) -> LLVMValue {
    assert!(llvm_get_insert_block(builder).is_some());
    unsafe { LLVMBuildOr(builder.0, lhs.into(), rhs.into(), to_c_str(name).as_ptr()).into() }
}

/// LLVMBuildXor
pub fn llvm_build_xor(
    builder: &LLVMBuilder,
    lhs: LLVMValue,
    rhs: LLVMValue,
    name: &str,
) -> LLVMValue {
    assert!(llvm_get_insert_block(builder).is_some());
    unsafe { LLVMBuildXor(builder.0, lhs.into(), rhs.into(), to_c_str(name).as_ptr()).into() }
}

/// LLVMBuildShl
pub fn llvm_build_shl(
    builder: &LLVMBuilder,
    lhs: LLVMValue,
    rhs: LLVMValue,
    name: &str,
) -> LLVMValue {
    assert!(llvm_get_insert_block(builder).is_some());
    unsafe { LLVMBuildShl(builder.0, lhs.into(), rhs.into(), to_c_str(name).as_ptr()).into() }
}

/// LLVMBuildArrayAlloca
pub fn llvm_build_array_alloca(
    builder: &LLVMBuilder,
    ty: LLVMType,
    size: LLVMValue,
    name: &str,
) -> LLVMValue {
    assert!(llvm_get_insert_block(builder).is_some());
    unsafe {
        LLVMBuildArrayAlloca(builder.0, ty.into(), size.into(), to_c_str(name).as_ptr()).into()
    }
}

/// LLVMBuildBitCast
pub fn llvm_build_bitcast(
    builder: &LLVMBuilder,
    val: LLVMValue,
    dest_ty: LLVMType,
    name: &str,
) -> LLVMValue {
    assert!(llvm_get_insert_block(builder).is_some());
    unsafe {
        LLVMBuildBitCast(
            builder.0,
            val.into(),
            dest_ty.into(),
            to_c_str(name).as_ptr(),
        )
        .into()
    }
}

/// LLVMBuildSExt
pub fn llvm_build_sext(
    builder: &LLVMBuilder,
    val: LLVMValue,
    dest_ty: LLVMType,
    name: &str,
) -> LLVMValue {
    assert!(llvm_get_insert_block(builder).is_some());
    unsafe {
        LLVMBuildSExt(
            builder.0,
            val.into(),
            dest_ty.into(),
            to_c_str(name).as_ptr(),
        )
        .into()
    }
}

/// LLVMBuildZExt
pub fn llvm_build_zext(
    builder: &LLVMBuilder,
    val: LLVMValue,
    dest_ty: LLVMType,
    name: &str,
) -> LLVMValue {
    assert!(llvm_get_insert_block(builder).is_some());
    unsafe {
        LLVMBuildZExt(
            builder.0,
            val.into(),
            dest_ty.into(),
            to_c_str(name).as_ptr(),
        )
        .into()
    }
}

/// LLVMBuildGEP2
pub fn llvm_build_gep2(
    builder: &LLVMBuilder,
    ty: LLVMType,
    ptr: LLVMValue,
    indices: &[LLVMValue],
    name: &str,
) -> LLVMValue {
    assert!(llvm_get_insert_block(builder).is_some());
    let mut indices: Vec<_> = indices.iter().cloned().map(Into::into).collect();
    unsafe {
        LLVMBuildGEP2(
            builder.0,
            ty.into(),
            ptr.into(),
            indices.as_mut_ptr(),
            indices.len().try_into().unwrap(),
            to_c_str(name).as_ptr(),
        )
        .into()
    }
}

/// LLVMBuildInsertValue
pub fn llvm_build_insert_value(
    builder: &LLVMBuilder,
    agg_val: LLVMValue,
    element_val: LLVMValue,
    index: u32,
    name: &str,
) -> LLVMValue {
    assert!(llvm_get_insert_block(builder).is_some());
    unsafe {
        LLVMBuildInsertValue(
            builder.0,
            agg_val.into(),
            element_val.into(),
            index,
            to_c_str(name).as_ptr(),
        )
        .into()
    }
}

/// LLVMBuildExtractValue
pub fn llvm_build_extract_value(
    builder: &LLVMBuilder,
    agg_val: LLVMValue,
    index: u32,
    name: &str,
) -> LLVMValue {
    assert!(llvm_get_insert_block(builder).is_some());
    unsafe {
        LLVMBuildExtractValue(builder.0, agg_val.into(), index, to_c_str(name).as_ptr()).into()
    }
}

/// LLVMAddIncoming
pub fn llvm_add_incoming(
    phi_node: LLVMValue,
    incoming_values: &[LLVMValue],
    incoming_blocks: &[LLVMBasicBlock],
) {
    assert!(llvm_is_a::phi_node(phi_node));
    assert!(incoming_values.len() == incoming_blocks.len());
    let mut incoming_values: Vec<LLVMValueRef> =
        incoming_values.iter().cloned().map(Into::into).collect();
    let mut incoming_blocks: Vec<_> = incoming_blocks.iter().cloned().map(Into::into).collect();
    unsafe {
        LLVMAddIncoming(
            phi_node.into(),
            incoming_values.as_mut_ptr(),
            incoming_blocks.as_mut_ptr(),
            incoming_blocks.len().try_into().unwrap(),
        )
    }
}

/// LLVMBuildCondBr
pub fn llvm_build_cond_br(
    builder: &LLVMBuilder,
    if_val: LLVMValue,
    then_block: LLVMBasicBlock,
    else_block: LLVMBasicBlock,
) -> LLVMValue {
    assert!(llvm_get_insert_block(builder).is_some());
    unsafe {
        LLVMBuildCondBr(
            builder.0,
            if_val.into(),
            then_block.into(),
            else_block.into(),
        )
        .into()
    }
}

/// LLVMBuildBr
pub fn llvm_build_br(builder: &LLVMBuilder, dest: LLVMBasicBlock) -> LLVMValue {
    assert!(llvm_get_insert_block(builder).is_some());
    unsafe { LLVMBuildBr(builder.0, dest.into()).into() }
}

/// LLVMBuildLoad2
pub fn llvm_build_load2(
    builder: &LLVMBuilder,
    ty: LLVMType,
    pointer_val: LLVMValue,
    name: &str,
) -> LLVMValue {
    assert!(llvm_get_insert_block(builder).is_some());
    unsafe {
        LLVMBuildLoad2(
            builder.0,
            ty.into(),
            pointer_val.into(),
            to_c_str(name).as_ptr(),
        )
        .into()
    }
}

/// LLVMBuildStore
pub fn llvm_build_store(builder: &LLVMBuilder, val: LLVMValue, ptr: LLVMValue) -> LLVMValue {
    assert!(llvm_get_insert_block(builder).is_some());
    unsafe { LLVMBuildStore(builder.0, val.into(), ptr.into()).into() }
}

/// LLVMBuildICmp
pub fn llvm_build_icmp(
    builder: &LLVMBuilder,
    op: LLVMIntPredicate,
    lhs: LLVMValue,
    rhs: LLVMValue,
    name: &str,
) -> LLVMValue {
    assert!(llvm_get_insert_block(builder).is_some());
    unsafe {
        LLVMBuildICmp(
            builder.0,
            op,
            lhs.into(),
            rhs.into(),
            to_c_str(name).as_ptr(),
        )
        .into()
    }
}

/// LLVMBuildRetVoid
pub fn llvm_build_ret_void(builder: &LLVMBuilder) -> LLVMValue {
    assert!(llvm_get_insert_block(builder).is_some());
    unsafe { LLVMBuildRetVoid(builder.0).into() }
}

/// LLVMBuildRet
pub fn llvm_build_ret(builder: &LLVMBuilder, val: LLVMValue) -> LLVMValue {
    assert!(llvm_get_insert_block(builder).is_some());
    unsafe { LLVMBuildRet(builder.0, val.into()).into() }
}

/// LLVMBuildPhi
pub fn llvm_build_phi(builder: &LLVMBuilder, ty: LLVMType, name: &str) -> LLVMValue {
    assert!(llvm_get_insert_block(builder).is_some());
    unsafe { LLVMBuildPhi(builder.0, ty.into(), to_c_str(name).as_ptr()).into() }
}

/// LLVMBuildCall2
pub fn llvm_build_call2(
    builder: &LLVMBuilder,
    ty: LLVMType,
    callee: LLVMValue,
    args: &[LLVMValue],
    name: &str,
) -> LLVMValue {
    assert!(llvm_get_insert_block(builder).is_some());
    let mut args: Vec<_> = args.iter().cloned().map(Into::into).collect();
    unsafe {
        LLVMBuildCall2(
            builder.0,
            ty.into(),
            callee.into(),
            args.as_mut_ptr(),
            args.len().try_into().unwrap(),
            to_c_str(name).as_ptr(),
        )
        .into()
    }
}

/// LLVMConstInt
pub fn llvm_const_int(int_ty: LLVMType, val: u64, sign_extend: bool) -> LLVMValue {
    assert!(llvm_get_type_kind(int_ty) == LLVMTypeKind::LLVMIntegerTypeKind);
    unsafe { LLVMConstInt(int_ty.into(), val, sign_extend as i32).into() }
}

/// LLVMGetUndef
pub fn llvm_get_undef(ty: LLVMType) -> LLVMValue {
    unsafe { LLVMGetUndef(ty.into()).into() }
}

/// LLVMAddFunction
pub fn llvm_add_function(module: &LLVMModule, name: &str, fn_ty: LLVMType) -> LLVMValue {
    assert!(llvm_get_type_kind(fn_ty) == LLVMTypeKind::LLVMFunctionTypeKind);
    unsafe { LLVMAddFunction(module.0, to_c_str(name).as_ptr(), fn_ty.into()).into() }
}

/// LLVMAppendBasicBlockInContext
pub fn llvm_append_basic_block_in_context(
    context: &LLVMContext,
    func: LLVMValue,
    name: &str,
) -> LLVMBasicBlock {
    assert!(llvm_is_a::function(func));
    unsafe { LLVMAppendBasicBlockInContext(context.0, func.into(), to_c_str(name).as_ptr()).into() }
}

/// LLVMGetCalledValue
pub fn llvm_get_called_value(inst: LLVMValue) -> LLVMValue {
    assert!(llvm_is_a::call_inst(inst) || llvm_is_a::invoke_inst(inst));
    unsafe { LLVMGetCalledValue(inst.into()).into() }
}

/// LLVMGetNumArgOperands
pub fn llvm_get_num_arg_operands(inst: LLVMValue) -> u32 {
    assert!(llvm_is_a::call_inst(inst) || llvm_is_a::invoke_inst(inst));
    unsafe { LLVMGetNumArgOperands(inst.into()) }
}

/// LLVMGetCalledFunctionType
pub fn llvm_get_called_function_type(inst: LLVMValue) -> LLVMType {
    assert!(llvm_is_a::call_inst(inst) || llvm_is_a::invoke_inst(inst));
    unsafe { LLVMGetCalledFunctionType(inst.into()).into() }
}

/// LLVMGetNUW
pub fn llvm_get_nuw(arith_inst: LLVMValue) -> bool {
    assert!(llvm_is_a::instruction(arith_inst));
    unsafe { LLVMGetNUW(arith_inst.into()).to_bool() }
}

/// LLVMGetNSW
pub fn llvm_get_nsw(arith_inst: LLVMValue) -> bool {
    assert!(llvm_is_a::instruction(arith_inst));
    unsafe { LLVMGetNSW(arith_inst.into()).to_bool() }
}

/// LLVMGetGEPSourceElementType
pub fn llvm_get_gep_source_element_type(gep_inst: LLVMValue) -> LLVMType {
    assert!(llvm_is_a::get_element_ptr_inst(gep_inst));
    unsafe { LLVMGetGEPSourceElementType(gep_inst.into()).into() }
}

/// LLVMGetNumIndices
pub fn llvm_get_num_indices(inst: LLVMValue) -> u32 {
    assert!(llvm_is_a::insert_value_inst(inst) || llvm_is_a::extract_value_inst(inst));
    unsafe { LLVMGetNumIndices(inst.into()) }
}

/// LLVMGetIndices
pub fn llvm_get_indices(inst: LLVMValue) -> Vec<u32> {
    assert!(llvm_is_a::insert_value_inst(inst) || llvm_is_a::extract_value_inst(inst));
    let num_indices = llvm_get_num_indices(inst);
    let indices = unsafe { LLVMGetIndices(inst.into()) };
    c_array_to_vec(indices, num_indices as usize)
}

/// RAII wrapper around LLVMModuleRef
pub struct LLVMModule(LLVMModuleRef);

impl Drop for LLVMModule {
    fn drop(&mut self) {
        unsafe { LLVMDisposeModule(self.0) }
    }
}

impl LLVMModule {
    pub fn new(module_id: &str, context: &LLVMContext) -> Self {
        Self(unsafe { LLVMModuleCreateWithNameInContext(to_c_str(module_id).as_ptr(), context.0) })
    }

    /// Parse IR in memory buffer to [LLVMModule]
    pub fn from_ir_in_memory_buffer(
        context: &LLVMContext,
        memory_buffer: LLVMMemoryBuffer,
    ) -> Result<LLVMModule, String> {
        let mut module_ref = MaybeUninit::uninit();
        let mut err_string = MaybeUninit::uninit();

        let success = unsafe {
            LLVMParseIRInContext(
                context.0,
                memory_buffer.memory_buffer_ref,
                module_ref.as_mut_ptr(),
                err_string.as_mut_ptr(),
            )
        };

        // LLVMParseIRInContext consumes the memory buffer.
        forget(memory_buffer);

        if success != 0 {
            unsafe {
                let err_str = err_string.assume_init();
                let err_string = cstr_to_string(err_str).unwrap();
                LLVMDisposeMessage(err_str);
                return Err(err_string);
            }
        }

        unsafe { Ok(LLVMModule(module_ref.assume_init())) }
    }

    /// Parse IR in file given by filename into a [LLVMModule]
    pub fn from_ir_in_file(context: &LLVMContext, filename: &str) -> Result<LLVMModule, String> {
        let memory_buffer = LLVMMemoryBuffer::from_file_name(filename)?;
        Self::from_ir_in_memory_buffer(context, memory_buffer)
    }

    /// Print [LLVMModule] to a text assembly file
    pub fn asm_to_file(&self, filename: &str) -> Result<(), String> {
        let mut err_string = MaybeUninit::uninit();
        let return_code = unsafe {
            LLVMPrintModuleToFile(self.0, to_c_str(filename).as_ptr(), err_string.as_mut_ptr())
        };

        if return_code == 1 {
            unsafe {
                let err_str = err_string.assume_init();
                let err_string = cstr_to_string(err_str).unwrap();
                LLVMDisposeMessage(err_str);
                return Err(err_string);
            }
        }

        Ok(())
    }

    /// Print this [LLVMModule] to a bitcode file
    pub fn bitcode_to_file(&self, filename: &str) -> Result<(), String> {
        unsafe {
            if LLVMWriteBitcodeToFile(self.0, to_c_str(filename).as_ptr()) == 0 {
                Ok(())
            } else {
                Err("Error writing bitcode to file".into())
            }
        }
    }

    /// Verify this module
    pub fn verify(&self) -> Result<(), String> {
        let mut err_string = MaybeUninit::uninit();
        let return_code = unsafe {
            LLVMVerifyModule(
                self.0,
                llvm_sys::analysis::LLVMVerifierFailureAction::LLVMReturnStatusAction,
                err_string.as_mut_ptr(),
            )
        };
        if return_code == 1 {
            unsafe {
                let err_str = err_string.assume_init();
                let err_string = cstr_to_string(err_str).unwrap();
                LLVMDisposeMessage(err_str);
                return Err(err_string);
            }
        }
        Ok(())
    }
}

pub struct LLVMMemoryBuffer {
    pub memory_buffer_ref: LLVMMemoryBufferRef,
}

impl LLVMMemoryBuffer {
    /// Create [LLVMMemoryBuffer] from a filename.
    pub fn from_file_name(name: &str) -> Result<LLVMMemoryBuffer, String> {
        let mut memory_buffer_ref = ptr::null_mut();
        let mut err_string = MaybeUninit::uninit();

        let return_code = unsafe {
            LLVMCreateMemoryBufferWithContentsOfFile(
                to_c_str(name).as_ptr(),
                &mut memory_buffer_ref,
                err_string.as_mut_ptr(),
            )
        };

        if return_code == 1 {
            unsafe {
                let err_str = err_string.assume_init();
                let err_string = cstr_to_string(err_str).unwrap();
                LLVMDisposeMessage(err_str);
                return Err(err_string);
            }
        }

        Ok(LLVMMemoryBuffer { memory_buffer_ref })
    }
}

impl Drop for LLVMMemoryBuffer {
    fn drop(&mut self) {
        unsafe { LLVMDisposeMemoryBuffer(self.memory_buffer_ref) }
    }
}
