//! Translate from LLVM-IR to pliron's LLVM dialect

use std::num::NonZero;

use llvm_sys::{LLVMIntPredicate, LLVMOpcode, LLVMTypeKind, LLVMValueKind};
use pliron::{
    basic_block::BasicBlock,
    builtin::{
        attributes::IntegerAttr,
        op_interfaces::{
            CallOpCallable, OneRegionInterface, OneResultInterface, SingleBlockRegionInterface,
        },
        ops::{FuncOp, ModuleOp},
        types::{FunctionType, IntegerType, Signedness},
    },
    context::{Context, Ptr},
    debug_info,
    identifier::{self, Identifier},
    input_err_noloc, input_error_noloc,
    linked_list::ContainsLinkedList,
    op::Op,
    operation::Operation,
    result::Result,
    r#type::{TypeObj, TypePtr},
    utils::apint::APInt,
    value::Value,
};
use rustc_hash::{FxHashMap, FxHashSet};
use thiserror::Error;

use crate::{
    attributes::{ICmpPredicateAttr, IntegerOverflowFlagsAttr},
    llvm_sys::core::{
        LLVMBasicBlock, LLVMModule, LLVMType, LLVMValue, basic_block_iter, function_iter,
        global_iter, incoming_iter, instruction_iter, llvm_const_int_get_zext_value,
        llvm_count_struct_element_types, llvm_get_aggregate_element, llvm_get_allocated_type,
        llvm_get_array_length2, llvm_get_basic_block_name, llvm_get_basic_block_terminator,
        llvm_get_called_function_type, llvm_get_called_value, llvm_get_const_opcode,
        llvm_get_element_type, llvm_get_gep_source_element_type, llvm_get_icmp_predicate,
        llvm_get_indices, llvm_get_initializer, llvm_get_instruction_opcode,
        llvm_get_instruction_parent, llvm_get_int_type_width, llvm_get_module_identifier,
        llvm_get_nsw, llvm_get_num_arg_operands, llvm_get_num_operands, llvm_get_nuw,
        llvm_get_operand, llvm_get_param_types, llvm_get_return_type,
        llvm_get_struct_element_types, llvm_get_struct_name, llvm_get_type_kind,
        llvm_get_value_kind, llvm_get_value_name, llvm_global_get_value_type, llvm_is_a,
        llvm_is_opaque_struct, llvm_print_value_to_string, llvm_type_of, llvm_value_as_basic_block,
        llvm_value_is_basic_block, param_iter,
    },
    op_interfaces::{BinArithOp, CastOpInterface, IntBinArithOpWithOverflowFlag},
    ops::{
        AShrOp, AddOp, AddressOfOp, AllocaOp, AndOp, BitcastOp, BrOp, CallOp, CondBrOp, ConstantOp,
        ExtractValueOp, GepIndex, GetElementPtrOp, GlobalOp, ICmpOp, InsertValueOp, IntToPtrOp,
        LShrOp, LoadOp, MulOp, OrOp, PtrToIntOp, ReturnOp, SDivOp, SExtOp, SRemOp, SelectOp, ShlOp,
        StoreOp, SubOp, SwitchCase, SwitchOp, TruncOp, UDivOp, URemOp, UndefOp, XorOp, ZExtOp,
        ZeroOp,
    },
    types::{ArrayType, PointerType, StructErr, StructType, VoidType},
};

fn convert_type(
    ctx: &mut Context,
    cctx: &mut ConversionContext,
    ty: LLVMType,
) -> Result<Ptr<TypeObj>> {
    let kind = llvm_get_type_kind(ty);
    match kind {
        LLVMTypeKind::LLVMArrayTypeKind => {
            let (element_ty, len) = (llvm_get_element_type(ty), llvm_get_array_length2(ty));
            let elem = convert_type(ctx, cctx, element_ty)?;
            Ok(ArrayType::get(ctx, elem, len).into())
        }
        LLVMTypeKind::LLVMFloatTypeKind => todo!(),
        LLVMTypeKind::LLVMFunctionTypeKind => {
            let return_type = convert_type(ctx, cctx, llvm_get_return_type(ty))?;
            let param_types = llvm_get_param_types(ty)
                .into_iter()
                .map(|ty| convert_type(ctx, cctx, ty))
                .collect::<Result<_>>()?;
            // TODO: Use llvm::types::FuncType.
            // Not already doing it because we don't have a corresponding llvm::ops::FuncOp.
            Ok(FunctionType::get(ctx, param_types, vec![return_type]).into())
        }
        LLVMTypeKind::LLVMIntegerTypeKind => {
            let bit_width = llvm_get_int_type_width(ty);
            Ok(IntegerType::get(ctx, bit_width, Signedness::Signless).into())
        }
        LLVMTypeKind::LLVMPointerTypeKind => Ok(PointerType::get(ctx).into()),
        LLVMTypeKind::LLVMStructTypeKind => {
            let name_opt: Option<Identifier> =
                llvm_get_struct_name(ty).map(|str| cctx.id_legaliser.legalise(&str));
            if llvm_is_opaque_struct(ty) {
                // Opaque structs must be named.
                let Some(name) = name_opt else {
                    return input_err_noloc!(StructErr::OpaqueAndAnonymousErr);
                };
                Ok(StructType::get_named(ctx, name, None)?.into())
            } else {
                let field_types = llvm_get_struct_element_types(ty)
                    .into_iter()
                    .map(|ty| convert_type(ctx, cctx, ty))
                    .collect::<Result<_>>()?;
                if let Some(name) = name_opt {
                    Ok(StructType::get_named(ctx, name, Some(field_types))?.into())
                } else {
                    Ok(StructType::get_unnamed(ctx, field_types).into())
                }
            }
        }
        LLVMTypeKind::LLVMVoidTypeKind => Ok(VoidType::get(ctx).into()),
        LLVMTypeKind::LLVMVectorTypeKind => todo!(),
        LLVMTypeKind::LLVMHalfTypeKind => todo!(),
        LLVMTypeKind::LLVMDoubleTypeKind => todo!(),
        LLVMTypeKind::LLVMX86_FP80TypeKind => todo!(),
        LLVMTypeKind::LLVMFP128TypeKind => todo!(),
        LLVMTypeKind::LLVMPPC_FP128TypeKind => todo!(),
        LLVMTypeKind::LLVMLabelTypeKind => todo!(),
        LLVMTypeKind::LLVMMetadataTypeKind => todo!(),
        LLVMTypeKind::LLVMTokenTypeKind => todo!(),
        LLVMTypeKind::LLVMScalableVectorTypeKind => todo!(),
        LLVMTypeKind::LLVMBFloatTypeKind => todo!(),
        LLVMTypeKind::LLVMX86_AMXTypeKind => todo!(),
        LLVMTypeKind::LLVMTargetExtTypeKind => todo!(),
    }
}

pub fn convert_ipredicate(ipred: LLVMIntPredicate) -> ICmpPredicateAttr {
    match ipred {
        LLVMIntPredicate::LLVMIntEQ => ICmpPredicateAttr::EQ,
        LLVMIntPredicate::LLVMIntNE => ICmpPredicateAttr::NE,
        LLVMIntPredicate::LLVMIntUGT => ICmpPredicateAttr::UGT,
        LLVMIntPredicate::LLVMIntUGE => ICmpPredicateAttr::UGE,
        LLVMIntPredicate::LLVMIntULT => ICmpPredicateAttr::ULT,
        LLVMIntPredicate::LLVMIntULE => ICmpPredicateAttr::ULE,
        LLVMIntPredicate::LLVMIntSGT => ICmpPredicateAttr::SGT,
        LLVMIntPredicate::LLVMIntSGE => ICmpPredicateAttr::SGE,
        LLVMIntPredicate::LLVMIntSLT => ICmpPredicateAttr::SLT,
        LLVMIntPredicate::LLVMIntSLE => ICmpPredicateAttr::SLE,
    }
}

/// Mapping from LLVM entities to pliron entities.
#[derive(Default)]
struct ConversionContext {
    // A map from LLVM's Values to pliron's Values.
    value_map: FxHashMap<LLVMValue, Value>,
    // A map from LLVM's basic blocks to plirons'.
    block_map: FxHashMap<LLVMBasicBlock, Ptr<BasicBlock>>,
    // Entry block of the region we're processing.
    entry_block: Option<Ptr<BasicBlock>>,
    // Identifier legaliser
    id_legaliser: identifier::Legaliser,
}

impl ConversionContext {
    /// Reset the value and block maps and set the entry block.
    /// Identifier::Legaliser remains unmodified.
    fn reset_for_region(&mut self, entry_block: Ptr<BasicBlock>) {
        self.entry_block = Some(entry_block);
        self.value_map.clear();
        self.block_map.clear();
    }
}

/// Get the successors of an LLVM block.
fn successors(block: LLVMBasicBlock) -> Vec<LLVMBasicBlock> {
    let Some(term) = llvm_get_basic_block_terminator(block) else {
        return vec![];
    };

    match llvm_get_instruction_opcode(term) {
        LLVMOpcode::LLVMBr => {
            if llvm_get_num_operands(term) == 1 {
                // Conditional branch
                vec![llvm_value_as_basic_block(llvm_get_operand(term, 0))]
            } else {
                assert!(llvm_get_num_operands(term) == 3);
                vec![
                    llvm_value_as_basic_block(llvm_get_operand(term, 1)),
                    llvm_value_as_basic_block(llvm_get_operand(term, 2)),
                ]
            }
        }
        LLVMOpcode::LLVMSwitch => {
            // The first two operands are the condition value and the default destination.
            // After that there are pairs of case value and destination.
            let num_cases = (llvm_get_num_operands(term) - 2) / 2;
            let mut succs = vec![llvm_value_as_basic_block(llvm_get_operand(term, 1))];
            for i in 0..num_cases {
                succs.push(llvm_value_as_basic_block(llvm_get_operand(
                    term,
                    2 + (2 * i) + 1,
                )));
            }
            succs
        }
        LLVMOpcode::LLVMRet => {
            // Return has no successors.
            vec![]
        }
        _ => {
            todo!(
                "Unsupported instruction: {}",
                llvm_print_value_to_string(term).unwrap_or_default()
            )
        }
    }
}

/// Return RPO ordering of blocks in an LLVM function.
fn rpo(function: LLVMValue) -> Vec<LLVMBasicBlock> {
    let visited = &mut FxHashSet::<LLVMBasicBlock>::default();
    let mut po = Vec::<LLVMBasicBlock>::new();

    fn walk(
        block: LLVMBasicBlock,
        visited: &mut FxHashSet<LLVMBasicBlock>,
        po: &mut Vec<LLVMBasicBlock>,
    ) {
        if !visited.insert(block) {
            // block already visited.
            return;
        }
        // Visit successors before visiting self.
        for succ in successors(block).into_iter() {
            walk(succ, visited, po);
        }
        // Visit self.
        po.push(block);
    }

    // Walk every block (not just entry) since we may have unreachable blocks.
    for block in basic_block_iter(function) {
        walk(block, visited, &mut po);
    }

    // RPO is the reverse of PO.
    po.reverse();
    po
}

#[derive(Error, Debug)]
pub enum ConversionErr {
    #[error("Unable to get operand with idx {0}")]
    OpdMissing(usize),
    #[error("Unable to get successor with idx {0}")]
    SuccMissing(usize),
    #[error("PHI node must have argument from predecessor block \"^{0}\"")]
    PhiArgMissing(String),
    #[error("Definition for value \"{0}\" not seen yet")]
    UndefinedValue(String),
    #[error("Block definition \"^{0}\" not seen yet")]
    UndefinedBlock(String),
    #[error("Integer constant has bit-width 0")]
    ZeroWidthIntConst,
}

/// If a value is a ConstantOp with integer type, return the value.
fn get_const_op_as_int(ctx: &Context, val: Value) -> Option<IntegerAttr> {
    let Value::OpResult { op, res_idx: _ } = val else {
        return None;
    };
    Operation::get_op(op, ctx)
        .downcast_ref::<ConstantOp>()
        .and_then(|const_op| {
            const_op
                .get_value(ctx)
                .downcast_ref::<IntegerAttr>()
                .cloned()
        })
}

/// If a value is a ConstantOp with a 32-bit integer type, return the value.
fn get_const_op_as_u32(ctx: &Context, val: Value) -> Option<u32> {
    get_const_op_as_int(ctx, val).and_then(|int_attr| {
        let int_ty = int_attr.get_type().deref(ctx);
        // LLVM integers are signless.
        (int_ty.is_signless() && int_ty.get_width() == 32).then(|| int_attr.get_value().to_u32())
    })
}

/// Checks if a constant has been processed already, and if not
/// converts it and puts it in the [ConversionContext::value_map].
fn process_constant(ctx: &mut Context, cctx: &mut ConversionContext, val: LLVMValue) -> Result<()> {
    if cctx.value_map.contains_key(&val) {
        return Ok(());
    }
    let ll_ty = llvm_type_of(val);
    let ty = convert_type(ctx, cctx, ll_ty)?;
    let entry_block = cctx.entry_block.unwrap();
    match llvm_get_value_kind(val) {
        LLVMValueKind::LLVMUndefValueValueKind => {
            let undef_op = UndefOp::new(ctx, ty);
            // Insert at the end of the entry block.
            BasicBlock::insert_op_before_terminator(entry_block, undef_op.get_operation(), ctx);
            cctx.value_map.insert(val, undef_op.get_result(ctx));
        }
        LLVMValueKind::LLVMConstantPointerNullValueKind => {
            let null_op = ZeroOp::new(ctx, ty);
            BasicBlock::insert_op_before_terminator(entry_block, null_op.get_operation(), ctx);
            cctx.value_map.insert(val, null_op.get_result(ctx));
        }
        LLVMValueKind::LLVMConstantIntValueKind => {
            // TODO: Zero extend or sign extend?
            let u64 = llvm_const_int_get_zext_value(val);
            let int_ty = TypePtr::<IntegerType>::from_ptr(ty, ctx)?;
            let width = int_ty.deref(ctx).get_width() as usize;
            if width == 0 {
                return input_err_noloc!(ConversionErr::ZeroWidthIntConst);
            }
            let val_attr =
                IntegerAttr::new(int_ty, APInt::from_u64(u64, NonZero::new(width).unwrap()));
            let const_op = ConstantOp::new(ctx, Box::new(val_attr));
            // Insert at the end of the entry block.
            BasicBlock::insert_op_before_terminator(entry_block, const_op.get_operation(), ctx);
            cctx.value_map.insert(val, const_op.get_result(ctx));
        }
        LLVMValueKind::LLVMConstantFPValueKind => todo!(),
        LLVMValueKind::LLVMConstantArrayValueKind
        | LLVMValueKind::LLVMConstantDataArrayValueKind => {
            fn get_operand(val: LLVMValue, index: u32) -> Result<LLVMValue> {
                if matches!(
                    llvm_get_value_kind(val),
                    LLVMValueKind::LLVMConstantDataArrayValueKind
                ) {
                    llvm_get_aggregate_element(val, index).ok_or_else(|| {
                        input_error_noloc!("LLVMConstantDataArrayValueKind does not have an element at index {index}")
                    })
                } else {
                    Ok(llvm_get_operand(val, index))
                }
            }
            let mut field_vals = vec![];
            let num_elements = llvm_get_array_length2(ll_ty);
            for i in 0..num_elements {
                let field_val = get_operand(val, i.try_into().unwrap())?;
                process_constant(ctx, cctx, field_val)?;
                let Some(m_val) = cctx.value_map.get(&field_val) else {
                    panic!("We just processed this constant, it must be in the map");
                };
                field_vals.push(*m_val);
            }
            // Starting with an Undef value, we insert elements, for each field.
            let undef_op = UndefOp::new(ctx, ty);
            BasicBlock::insert_op_before_terminator(entry_block, undef_op.get_operation(), ctx);
            let (ctx, const_array) = field_vals.iter().enumerate().try_fold(
                (ctx, undef_op.get_operation()),
                |(ctx, acc), (field_idx, field_val)| -> Result<_> {
                    let acc_val = acc.deref(ctx).get_result(0);
                    let insert_op = InsertValueOp::new(
                        ctx,
                        acc_val,
                        *field_val,
                        vec![field_idx.try_into().unwrap()],
                    )
                    .get_operation();
                    insert_op.insert_after(ctx, acc);
                    Ok((ctx, insert_op))
                },
            )?;

            cctx.value_map
                .insert(val, const_array.deref(ctx).get_result(0));
        }
        LLVMValueKind::LLVMConstantStructValueKind => {
            let mut field_vals = vec![];
            let num_fields = llvm_count_struct_element_types(ll_ty);
            for i in 0..num_fields {
                let field_val = llvm_get_operand(val, i);
                process_constant(ctx, cctx, field_val)?;
                let Some(m_val) = cctx.value_map.get(&field_val) else {
                    panic!("We just processed this constant, it must be in the map");
                };
                field_vals.push(*m_val);
            }
            // Starting with an Undef value, we insert elements, for each field.
            let undef_op = UndefOp::new(ctx, ty);
            BasicBlock::insert_op_before_terminator(entry_block, undef_op.get_operation(), ctx);
            let (ctx, const_struct) = field_vals.iter().enumerate().try_fold(
                (ctx, undef_op.get_operation()),
                |(ctx, acc), (field_idx, field_val)| -> Result<_> {
                    let acc_val = acc.deref(ctx).get_result(0);
                    let insert_op = InsertValueOp::new(
                        ctx,
                        acc_val,
                        *field_val,
                        vec![field_idx.try_into().unwrap()],
                    )
                    .get_operation();
                    insert_op.insert_after(ctx, acc);
                    Ok((ctx, insert_op))
                },
            )?;

            cctx.value_map
                .insert(val, const_struct.deref(ctx).get_result(0));
        }
        LLVMValueKind::LLVMConstantExprValueKind => {
            let opcode = llvm_get_const_opcode(val);
            match opcode {
                LLVMOpcode::LLVMBitCast => {
                    let opd = llvm_get_operand(val, 0);
                    process_constant(ctx, cctx, opd)?;
                    let Some(m_val) = cctx.value_map.get(&opd) else {
                        panic!("We just processed this constant, it must be in the map");
                    };
                    let cast_op = BitcastOp::new(ctx, *m_val, ty);
                    BasicBlock::insert_op_before_terminator(
                        entry_block,
                        cast_op.get_operation(),
                        ctx,
                    );
                    cctx.value_map.insert(val, cast_op.get_result(ctx));
                }
                LLVMOpcode::LLVMIntToPtr => {
                    let opd = llvm_get_operand(val, 0);
                    process_constant(ctx, cctx, opd)?;
                    let Some(m_val) = cctx.value_map.get(&opd) else {
                        panic!("We just processed this constant, it must be in the map");
                    };
                    let cast_op = IntToPtrOp::new(ctx, *m_val, ty);
                    BasicBlock::insert_op_before_terminator(
                        entry_block,
                        cast_op.get_operation(),
                        ctx,
                    );
                    cctx.value_map.insert(val, cast_op.get_result(ctx));
                }
                LLVMOpcode::LLVMPtrToInt => {
                    let opd = llvm_get_operand(val, 0);
                    process_constant(ctx, cctx, opd)?;
                    let Some(m_val) = cctx.value_map.get(&opd) else {
                        panic!("We just processed this constant, it must be in the map");
                    };
                    let cast_op = PtrToIntOp::new(ctx, *m_val, ty);
                    BasicBlock::insert_op_before_terminator(
                        entry_block,
                        cast_op.get_operation(),
                        ctx,
                    );
                    cctx.value_map.insert(val, cast_op.get_result(ctx));
                }
                LLVMOpcode::LLVMGetElementPtr => {
                    let base = llvm_get_operand(val, 0);
                    process_constant(ctx, cctx, base)?;
                    let Some(m_base) = cctx.value_map.get(&base).cloned() else {
                        panic!("We just processed this constant, it must be in the map");
                    };
                    let mut indices = vec![];
                    for i in 1..llvm_get_num_operands(val) {
                        let opd = llvm_get_operand(val, i);
                        process_constant(ctx, cctx, opd)?;
                        let Some(m_val) = cctx.value_map.get(&opd) else {
                            panic!("We just processed this constant, it must be in the map");
                        };
                        if let Some(c) = get_const_op_as_u32(ctx, *m_val) {
                            indices.push(GepIndex::Constant(c));
                        } else {
                            indices.push(GepIndex::Value(*m_val));
                        }
                    }
                    let src_elm_type =
                        convert_type(ctx, cctx, llvm_get_gep_source_element_type(val))?;
                    let gep_op = GetElementPtrOp::new(ctx, m_base, indices, src_elm_type)?;
                    BasicBlock::insert_op_before_terminator(
                        entry_block,
                        gep_op.get_operation(),
                        ctx,
                    );
                    cctx.value_map.insert(val, gep_op.get_result(ctx));
                }
                LLVMOpcode::LLVMAdd | LLVMOpcode::LLVMSub => {
                    let (lhs, rhs) = (llvm_get_operand(val, 0), llvm_get_operand(val, 1));
                    process_constant(ctx, cctx, lhs)?;
                    process_constant(ctx, cctx, rhs)?;
                    let Some(m_lhs) = cctx.value_map.get(&lhs).cloned() else {
                        panic!("We just processed this constant, it must be in the map");
                    };
                    let Some(m_rhs) = cctx.value_map.get(&rhs).cloned() else {
                        panic!("We just processed this constant, it must be in the map");
                    };
                    // `Instruction *ConstantExpr::getAsInstruction() const ` just sets no flags.
                    let flags = IntegerOverflowFlagsAttr::default();
                    let (op, res_val) = if opcode == LLVMOpcode::LLVMAdd {
                        let op = AddOp::new(ctx, m_lhs, m_rhs);
                        op.set_integer_overflow_flag(ctx, flags);
                        (op.get_operation(), op.get_result(ctx))
                    } else {
                        let op = SubOp::new(ctx, m_lhs, m_rhs);
                        op.set_integer_overflow_flag(ctx, flags);
                        (op.get_operation(), op.get_result(ctx))
                    };
                    BasicBlock::insert_op_before_terminator(entry_block, op, ctx);
                    cctx.value_map.insert(val, res_val);
                }
                _ => todo!(),
            }
        }
        LLVMValueKind::LLVMGlobalVariableValueKind => {
            let global_name = llvm_get_value_name(val).unwrap_or_default();
            let global_name = cctx.id_legaliser.legalise(&global_name);
            let global_op = AddressOfOp::new(ctx, global_name);
            BasicBlock::insert_op_before_terminator(entry_block, global_op.get_operation(), ctx);
            cctx.value_map.insert(val, global_op.get_result(ctx));
        }
        LLVMValueKind::LLVMConstantVectorValueKind => todo!(),
        _ => (),
    }
    Ok(())
}

fn convert_operands(
    ctx: &mut Context,
    cctx: &mut ConversionContext,
    operands: &[LLVMValue],
) -> Result<(Vec<Value>, Vec<Ptr<BasicBlock>>)> {
    let mut opds = vec![];
    let mut succs = vec![];

    for opd in operands.iter().cloned() {
        if !llvm_value_is_basic_block(opd) {
            process_constant(ctx, cctx, opd)?;
            if let Some(m_val) = cctx.value_map.get(&opd) {
                opds.push(*m_val);
            } else {
                return input_err_noloc!(ConversionErr::UndefinedValue(
                    llvm_get_value_name(opd).unwrap_or_default()
                ));
            }
        } else {
            let block = llvm_value_as_basic_block(opd);
            let Some(m_block) = cctx.block_map.get(&block) else {
                return input_err_noloc!(ConversionErr::UndefinedBlock(
                    llvm_get_basic_block_name(block).unwrap_or_default()
                ));
            };
            succs.push(*m_block);
        }
    }
    Ok((opds, succs))
}

fn get_operand<T: Clone>(opds: &[T], idx: usize) -> Result<T> {
    opds.get(idx)
        .ok_or(input_error_noloc!(ConversionErr::OpdMissing(idx)))
        .cloned()
}

/// Compute the arguments to be passed when branching from `src` to `dest`.
fn convert_branch_args(
    ctx: &mut Context,
    cctx: &mut ConversionContext,
    src_block: LLVMBasicBlock,
    dst_block: LLVMBasicBlock,
) -> Result<Vec<Value>> {
    let mut args = vec![];
    for inst in instruction_iter(dst_block) {
        if llvm_is_a::phi_node(inst) {
            let Some((incoming_val, _)) =
                incoming_iter(inst).find(|(_, block)| *block == src_block)
            else {
                return input_err_noloc!(ConversionErr::PhiArgMissing(
                    llvm_get_basic_block_name(src_block).unwrap_or_default()
                ));
            };
            process_constant(ctx, cctx, incoming_val)?;
            let Some(m_incoming_val) = cctx.value_map.get(&incoming_val) else {
                return input_err_noloc!(ConversionErr::UndefinedValue(
                    llvm_get_value_name(incoming_val).unwrap_or_default()
                ));
            };
            args.push(*m_incoming_val)
        } else {
            // PHIs are at the start of the block.
            break;
        }
    }
    Ok(args)
}

fn convert_call(
    ctx: &mut Context,
    cctx: &mut ConversionContext,
    inst: LLVMValue,
) -> Result<Ptr<Operation>> {
    let llvm_operands: Vec<_> = (0..llvm_get_num_arg_operands(inst))
        .map(|opd_idx| llvm_get_operand(inst, opd_idx))
        .collect();
    let (args, _) = convert_operands(ctx, cctx, &llvm_operands)?;

    let callee = llvm_get_called_value(inst);
    let callee = if llvm_is_a::function(callee) {
        let fn_name = llvm_get_value_name(callee)
            .map(|name| cctx.id_legaliser.legalise(&name))
            .expect("Unable to obtain valid function name");
        CallOpCallable::Direct(fn_name)
    } else {
        let (callee_converted, _) = convert_operands(ctx, cctx, &[callee])?;
        CallOpCallable::Indirect(callee_converted[0])
    };

    let callee_ty = llvm_get_called_function_type(inst);
    let callee_ty: TypePtr<FunctionType> =
        convert_type(ctx, cctx, callee_ty).and_then(|ty| TypePtr::from_ptr(ty, ctx))?;
    Ok(CallOp::new(ctx, callee, callee_ty, args).get_operation())
}

fn convert_instruction(
    ctx: &mut Context,
    cctx: &mut ConversionContext,
    inst: LLVMValue,
) -> Result<Ptr<Operation>> {
    if llvm_is_a::call_inst(inst) {
        return convert_call(ctx, cctx, inst);
    }

    fn get_integer_overflow_flag(inst: LLVMValue) -> IntegerOverflowFlagsAttr {
        let mut flags = IntegerOverflowFlagsAttr::default();
        if llvm_get_nsw(inst) {
            flags.nsw = true;
        }
        if llvm_get_nuw(inst) {
            flags.nuw = true;
        }
        flags
    }

    let llvm_operands: Vec<_> = (0..llvm_get_num_operands(inst))
        .map(|opd_idx| llvm_get_operand(inst, opd_idx))
        .collect();

    let (ref opds, ref succs) = convert_operands(ctx, cctx, &llvm_operands)?;
    match llvm_get_instruction_opcode(inst) {
        LLVMOpcode::LLVMAdd => {
            let (lhs, rhs) = (get_operand(opds, 0)?, get_operand(opds, 1)?);
            Ok(
                AddOp::new_with_overflow_flag(ctx, lhs, rhs, get_integer_overflow_flag(inst))
                    .get_operation(),
            )
        }
        LLVMOpcode::LLVMAddrSpaceCast => todo!(),
        LLVMOpcode::LLVMAlloca => {
            let elem_type = convert_type(ctx, cctx, llvm_get_allocated_type(inst))?;
            let size = get_operand(opds, 0)?;
            Ok(AllocaOp::new(ctx, elem_type, size).get_operation())
        }
        LLVMOpcode::LLVMAnd => {
            let (lhs, rhs) = (get_operand(opds, 0)?, get_operand(opds, 1)?);
            Ok(AndOp::new(ctx, lhs, rhs).get_operation())
        }
        LLVMOpcode::LLVMAShr => {
            let (lhs, rhs) = (get_operand(opds, 0)?, get_operand(opds, 1)?);
            Ok(AShrOp::new(ctx, lhs, rhs).get_operation())
        }
        LLVMOpcode::LLVMAtomicCmpXchg => todo!(),
        LLVMOpcode::LLVMAtomicRMW => todo!(),
        LLVMOpcode::LLVMBitCast => {
            let arg = get_operand(opds, 0)?;
            let res_ty = convert_type(ctx, cctx, llvm_type_of(inst))?;
            Ok(BitcastOp::new(ctx, arg, res_ty).get_operation())
        }
        LLVMOpcode::LLVMBr => {
            if !opds.is_empty() {
                assert!(
                    succs.len() == 2,
                    "Conditional branch must have two successors"
                );
                let true_dest_opds = convert_branch_args(
                    ctx,
                    cctx,
                    llvm_get_instruction_parent(inst).unwrap(),
                    llvm_value_as_basic_block(llvm_get_operand(inst, 2)),
                )?;
                let false_dest_opds = convert_branch_args(
                    ctx,
                    cctx,
                    llvm_get_instruction_parent(inst).unwrap(),
                    llvm_value_as_basic_block(llvm_get_operand(inst, 1)),
                )?;
                Ok(CondBrOp::new(
                    ctx,
                    get_operand(opds, 0)?,
                    get_operand(succs, 1)?,
                    true_dest_opds,
                    get_operand(succs, 0)?,
                    false_dest_opds,
                )
                .get_operation())
            } else {
                let dest_opds = convert_branch_args(
                    ctx,
                    cctx,
                    llvm_get_instruction_parent(inst).unwrap(),
                    llvm_value_as_basic_block(llvm_get_operand(inst, 0)),
                )?;
                Ok(BrOp::new(ctx, get_operand(succs, 0)?, dest_opds).get_operation())
            }
        }
        LLVMOpcode::LLVMCall => {
            unreachable!("Should've already been processed separately")
        }
        LLVMOpcode::LLVMCallBr => todo!(),
        LLVMOpcode::LLVMCatchPad => todo!(),
        LLVMOpcode::LLVMCatchRet => todo!(),
        LLVMOpcode::LLVMCatchSwitch => todo!(),
        LLVMOpcode::LLVMCleanupPad => todo!(),
        LLVMOpcode::LLVMCleanupRet => todo!(),
        LLVMOpcode::LLVMExtractElement => todo!(),
        LLVMOpcode::LLVMFNeg => todo!(),
        LLVMOpcode::LLVMFAdd => todo!(),
        LLVMOpcode::LLVMFCmp => todo!(),
        LLVMOpcode::LLVMFDiv => todo!(),
        LLVMOpcode::LLVMFence => todo!(),
        LLVMOpcode::LLVMFMul => todo!(),
        LLVMOpcode::LLVMFPExt => todo!(),
        LLVMOpcode::LLVMFPToSI => todo!(),
        LLVMOpcode::LLVMFPToUI => todo!(),
        LLVMOpcode::LLVMFPTrunc => todo!(),
        LLVMOpcode::LLVMFreeze => todo!(),
        LLVMOpcode::LLVMFRem => todo!(),
        LLVMOpcode::LLVMFSub => todo!(),
        LLVMOpcode::LLVMGetElementPtr => {
            let mut opds = opds.iter();
            let base = opds
                .next()
                .ok_or_else(|| input_error_noloc!(ConversionErr::OpdMissing(0)))?;
            let indices = opds
                .map(|v| {
                    if let Some(c) = get_const_op_as_u32(ctx, *v) {
                        GepIndex::Constant(c)
                    } else {
                        GepIndex::Value(*v)
                    }
                })
                .collect::<Vec<_>>();
            let src_elm_type = convert_type(ctx, cctx, llvm_get_gep_source_element_type(inst))?;
            Ok(GetElementPtrOp::new(ctx, *base, indices, src_elm_type)?.get_operation())
        }
        LLVMOpcode::LLVMICmp => {
            let pred = convert_ipredicate(llvm_get_icmp_predicate(inst));
            Ok(
                ICmpOp::new(ctx, pred, get_operand(opds, 0)?, get_operand(opds, 1)?)
                    .get_operation(),
            )
        }
        LLVMOpcode::LLVMIndirectBr => todo!(),
        LLVMOpcode::LLVMInsertElement => todo!(),
        LLVMOpcode::LLVMInsertValue => {
            let (aggr, val) = (get_operand(opds, 0)?, get_operand(opds, 1)?);
            let indices = llvm_get_indices(inst);
            Ok(InsertValueOp::new(ctx, aggr, val, indices).get_operation())
        }
        LLVMOpcode::LLVMExtractValue => {
            let aggr = get_operand(opds, 0)?;
            let indices = llvm_get_indices(inst);
            Ok(ExtractValueOp::new(ctx, aggr, indices)?.get_operation())
        }
        LLVMOpcode::LLVMIntToPtr => {
            let arg = get_operand(opds, 0)?;
            let res_ty = convert_type(ctx, cctx, llvm_type_of(inst))?;
            Ok(IntToPtrOp::new(ctx, arg, res_ty).get_operation())
        }
        LLVMOpcode::LLVMInvoke => todo!(),
        LLVMOpcode::LLVMLandingPad => todo!(),
        LLVMOpcode::LLVMLoad => {
            let res_ty = convert_type(ctx, cctx, llvm_type_of(inst))?;
            Ok(LoadOp::new(ctx, get_operand(opds, 0)?, res_ty).get_operation())
        }
        LLVMOpcode::LLVMLShr => {
            let (lhs, rhs) = (get_operand(opds, 0)?, get_operand(opds, 1)?);
            Ok(LShrOp::new(ctx, lhs, rhs).get_operation())
        }
        LLVMOpcode::LLVMMul => {
            let (lhs, rhs) = (get_operand(opds, 0)?, get_operand(opds, 1)?);
            Ok(
                MulOp::new_with_overflow_flag(ctx, lhs, rhs, get_integer_overflow_flag(inst))
                    .get_operation(),
            )
        }
        LLVMOpcode::LLVMOr => {
            let (lhs, rhs) = (get_operand(opds, 0)?, get_operand(opds, 1)?);
            Ok(OrOp::new(ctx, lhs, rhs).get_operation())
        }
        LLVMOpcode::LLVMPHI => {
            unreachable!("PHI nodes must already be handled")
        }
        LLVMOpcode::LLVMPtrToInt => {
            let arg = get_operand(opds, 0)?;
            let res_ty = convert_type(ctx, cctx, llvm_type_of(inst))?;
            Ok(PtrToIntOp::new(ctx, arg, res_ty).get_operation())
        }
        LLVMOpcode::LLVMResume => todo!(),
        LLVMOpcode::LLVMRet => {
            let retval = if llvm_get_num_operands(inst) == 1 {
                Some(get_operand(opds, 0)?)
            } else {
                None
            };
            Ok(ReturnOp::new(ctx, retval).get_operation())
        }
        LLVMOpcode::LLVMSDiv => {
            let (lhs, rhs) = (get_operand(opds, 0)?, get_operand(opds, 1)?);
            Ok(SDivOp::new(ctx, lhs, rhs).get_operation())
        }
        LLVMOpcode::LLVMSelect => {
            let (cond, true_val, false_val) = (
                get_operand(opds, 0)?,
                get_operand(opds, 1)?,
                get_operand(opds, 2)?,
            );
            Ok(SelectOp::new(ctx, cond, true_val, false_val).get_operation())
        }
        LLVMOpcode::LLVMSExt => {
            let arg = get_operand(opds, 0)?;
            let res_ty = convert_type(ctx, cctx, llvm_type_of(inst))?;
            Ok(SExtOp::new(ctx, arg, res_ty).get_operation())
        }
        LLVMOpcode::LLVMZExt => {
            let arg = get_operand(opds, 0)?;
            let res_ty = convert_type(ctx, cctx, llvm_type_of(inst))?;
            Ok(ZExtOp::new(ctx, arg, res_ty).get_operation())
        }
        LLVMOpcode::LLVMTrunc => {
            let arg = get_operand(opds, 0)?;
            let res_ty = convert_type(ctx, cctx, llvm_type_of(inst))?;
            Ok(TruncOp::new(ctx, arg, res_ty).get_operation())
        }
        LLVMOpcode::LLVMShl => {
            let (lhs, rhs) = (get_operand(opds, 0)?, get_operand(opds, 1)?);
            Ok(
                ShlOp::new_with_overflow_flag(ctx, lhs, rhs, get_integer_overflow_flag(inst))
                    .get_operation(),
            )
        }
        LLVMOpcode::LLVMShuffleVector => todo!(),
        LLVMOpcode::LLVMSIToFP => todo!(),
        LLVMOpcode::LLVMSRem => {
            let (lhs, rhs) = (get_operand(opds, 0)?, get_operand(opds, 1)?);
            Ok(SRemOp::new(ctx, lhs, rhs).get_operation())
        }
        LLVMOpcode::LLVMStore => {
            let (value_opd, ptr_opd) = (get_operand(opds, 0)?, get_operand(opds, 1)?);
            Ok(StoreOp::new(ctx, value_opd, ptr_opd).get_operation())
        }
        LLVMOpcode::LLVMSub => {
            let (lhs, rhs) = (get_operand(opds, 0)?, get_operand(opds, 1)?);
            Ok(
                SubOp::new_with_overflow_flag(ctx, lhs, rhs, get_integer_overflow_flag(inst))
                    .get_operation(),
            )
        }
        LLVMOpcode::LLVMSwitch => {
            let cond = get_operand(opds, 0)?;
            let default_dest = succs
                .first()
                .ok_or_else(|| input_error_noloc!(ConversionErr::SuccMissing(0)))?;
            let cases = opds
                .iter()
                // Skip the first operand which is the condition
                .skip(1)
                // Skip the first successor which is the default destination
                .zip(succs.iter().skip(1))
                .enumerate()
                .map(|(case_idx, (case_val, dest_block))| {
                    let case_val = get_const_op_as_int(ctx, *case_val).ok_or_else(|| {
                        input_error_noloc!("Switch case value must be a constant integer")
                    })?;
                    let case_idx: u32 = case_idx.try_into().unwrap();
                    let llvm_dest =
                        llvm_value_as_basic_block(llvm_get_operand(inst, 2 + (2 * case_idx) + 1));
                    assert!(
                        cctx.block_map.get(&llvm_dest).unwrap() == dest_block,
                        "Switch case destination block does not match the expected block"
                    );
                    let case_args = convert_branch_args(
                        ctx,
                        cctx,
                        llvm_get_instruction_parent(inst).unwrap(),
                        llvm_dest,
                    )?;
                    Ok(SwitchCase {
                        value: case_val,
                        dest: *dest_block,
                        dest_opds: case_args,
                    })
                })
                .collect::<Result<Vec<_>>>()?;
            let default_dest_args = convert_branch_args(
                ctx,
                cctx,
                llvm_get_instruction_parent(inst).unwrap(),
                llvm_value_as_basic_block(llvm_get_operand(inst, 1)),
            )?;
            Ok(SwitchOp::new(ctx, cond, *default_dest, default_dest_args, cases).get_operation())
        }
        LLVMOpcode::LLVMUDiv => {
            let (lhs, rhs) = (get_operand(opds, 0)?, get_operand(opds, 1)?);
            Ok(UDivOp::new(ctx, lhs, rhs).get_operation())
        }
        LLVMOpcode::LLVMUIToFP => todo!(),
        LLVMOpcode::LLVMUnreachable => todo!(),
        LLVMOpcode::LLVMURem => {
            let (lhs, rhs) = (get_operand(opds, 0)?, get_operand(opds, 1)?);
            Ok(URemOp::new(ctx, lhs, rhs).get_operation())
        }
        LLVMOpcode::LLVMUserOp1 => todo!(),
        LLVMOpcode::LLVMUserOp2 => todo!(),
        LLVMOpcode::LLVMVAArg => todo!(),
        LLVMOpcode::LLVMXor => {
            let (lhs, rhs) = (get_operand(opds, 0)?, get_operand(opds, 1)?);
            Ok(XorOp::new(ctx, lhs, rhs).get_operation())
        }
    }
}

/// Convert [LLVMBasicBlock] to pliron's [BasicBlock].
fn convert_block(
    ctx: &mut Context,
    cctx: &mut ConversionContext,
    block: LLVMBasicBlock,
    m_block: Ptr<BasicBlock>,
) -> Result<()> {
    for inst in instruction_iter(block) {
        if llvm_get_instruction_opcode(inst) == LLVMOpcode::LLVMPHI {
            let ty = convert_type(ctx, cctx, llvm_type_of(inst))?;
            let arg_idx = m_block.deref_mut(ctx).add_argument(ty);
            cctx.value_map
                .insert(inst, m_block.deref(ctx).get_argument(arg_idx));
        } else {
            let m_inst = convert_instruction(ctx, cctx, inst)?;
            m_inst.insert_at_back(m_block, ctx);
            let m_inst_result = m_inst.deref(ctx).results().next();
            // LLVM instructions have at most one result.
            if let Some(result) = m_inst_result {
                if let Some(res_name) = llvm_get_value_name(inst).filter(|name| !name.is_empty()) {
                    let res_name = cctx.id_legaliser.legalise(&res_name);
                    debug_info::set_operation_result_name(ctx, m_inst, 0, res_name);
                }
                cctx.value_map.insert(inst, result);
            }
        }
    }
    Ok(())
}

fn convert_function(
    ctx: &mut Context,
    cctx: &mut ConversionContext,
    function: LLVMValue,
) -> Result<FuncOp> {
    assert!(llvm_is_a::function(function));
    let name = llvm_get_value_name(function)
        .map(|name| cctx.id_legaliser.legalise(&name))
        .expect("Expected functions to have names");
    let fn_ty = convert_type(ctx, cctx, llvm_global_get_value_type(function))?;
    let fn_ty = TypePtr::from_ptr(fn_ty, ctx)?;
    // Create a new FuncOp, which also creates an entry block with the right parameters.
    let m_func = FuncOp::new(ctx, name, fn_ty);
    let m_func_reg = m_func.get_region(ctx);

    let m_entry_block = m_func.get_entry_block(ctx);
    cctx.reset_for_region(m_entry_block);

    let blocks = rpo(function);
    // Map entry block
    let mut blocks_iter = blocks.iter();
    let Some(entry) = blocks_iter.next() else {
        return Ok(m_func);
    };

    cctx.block_map.insert(*entry, m_entry_block);
    {
        let val_map = &mut cctx.value_map;
        let m_entry_block_ref = m_entry_block.deref(ctx);
        // Map function args to entry block args.
        for (arg_idx, arg) in param_iter(function).enumerate() {
            val_map.insert(arg, m_entry_block_ref.get_argument(arg_idx));
        }
    }

    // Create, place and map rest of the blocks.
    for block in blocks_iter {
        let label = llvm_get_basic_block_name(*block)
            .filter(|name| !name.is_empty())
            .map(|name| cctx.id_legaliser.legalise(&name));
        let m_block = BasicBlock::new(ctx, label, vec![]);
        m_block.insert_at_back(m_func_reg, ctx);
        cctx.block_map.insert(*block, m_block);
    }

    // Finally, convert all blocks
    for block in blocks {
        let m_block = *cctx
            .block_map
            .get(&block)
            .expect("We have an unmapped block !");
        convert_block(ctx, cctx, block, m_block)?;
    }

    Ok(m_func)
}

fn convert_global(
    ctx: &mut Context,
    cctx: &mut ConversionContext,
    global: LLVMValue,
) -> Result<GlobalOp> {
    let name = llvm_get_value_name(global).unwrap_or_default();
    let name = cctx.id_legaliser.legalise(&name);

    let ty = convert_type(
        ctx,
        &mut ConversionContext::default(),
        llvm_global_get_value_type(global),
    )?;

    let op = GlobalOp::new(ctx, name, ty);

    if let Some(init) = llvm_get_initializer(global) {
        // TODO: Use attribute based initializer for simple constants.
        let init_region = op.add_initializer_region(ctx);
        let entry_block = init_region.deref(ctx).iter(ctx).next().unwrap();
        cctx.reset_for_region(entry_block);

        // Convert the initializer.
        process_constant(ctx, cctx, init)?;
        let Some(m_val) = cctx.value_map.get(&init) else {
            panic!("We just processed this constant, it must be in the map");
        };

        let return_op = ReturnOp::new(ctx, Some(*m_val));
        return_op.get_operation().insert_at_back(entry_block, ctx);
    }

    Ok(op)
}

/// Convert [LLVMModule] to [ModuleOp].
pub fn convert_module(ctx: &mut Context, module: &LLVMModule) -> Result<ModuleOp> {
    let cctx = &mut ConversionContext::default();

    let module_name = llvm_get_module_identifier(module).unwrap_or_default();
    let module_name = cctx.id_legaliser.legalise(&module_name);

    let m = ModuleOp::new(ctx, module_name);

    // Convert globals.
    for gv in global_iter(module) {
        let m_gv = convert_global(ctx, cctx, gv)?;
        m.append_operation(ctx, m_gv.get_operation(), 0);
    }

    // Convert functions.
    for fun in function_iter(module) {
        let m_fun = convert_function(ctx, cctx, fun)?;
        m.append_operation(ctx, m_fun.get_operation(), 0);
    }
    Ok(m)
}
