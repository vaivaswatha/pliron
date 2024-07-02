//! Translate from [inkwell] LLVM-IR to pliron's LLVM dialect

use std::ffi::CStr;

use apint::ApInt;
use inkwell::{
    basic_block::BasicBlock as IWBasicBlock,
    module::Module as IWModule,
    types::{AnyType, AnyTypeEnum},
    values::{
        AnyValue, AnyValueEnum, BasicValue, BasicValueEnum, FunctionValue, InstructionOpcode,
        InstructionValue, PhiValue,
    },
    IntPredicate,
};
use pliron::{
    basic_block::BasicBlock,
    builtin::{
        attributes::IntegerAttr,
        op_interfaces::{OneRegionInterface, OneResultInterface, SingleBlockRegionInterface},
        ops::{FuncOp, ModuleOp},
        types::{FunctionType, IntegerType},
    },
    context::{Context, Ptr},
    identifier::Identifier,
    input_err_noloc, input_error_noloc,
    op::Op,
    operation::Operation,
    r#type::{TypeObj, TypePtr},
    result::Result,
    use_def_lists::Value,
};
use rustc_hash::{FxHashMap, FxHashSet};
use thiserror::Error;

use crate::{
    attributes::ICmpPredicateAttr,
    op_interfaces::BinArithOp,
    ops::{
        AShrOp, AddOp, AllocaOp, AndOp, BitcastOp, BrOp, CondBrOp, ConstantOp, ICmpOp, LShrOp,
        LoadOp, MulOp, OrOp, ReturnOp, SDivOp, SRemOp, ShlOp, StoreOp, SubOp, UDivOp, URemOp,
        UndefOp, XorOp,
    },
    types::{ArrayType, PointerType, StructErr, StructType, VoidType},
};

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
            Ok(ArrayType::get(ctx, elem, aty.len() as u64).into())
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
            Ok(FunctionType::get(ctx, param_types, vec![return_type]).into())
        }
        AnyTypeEnum::IntType(ity) => Ok(IntegerType::get(
            ctx,
            ity.get_bit_width(),
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
                let name: Identifier = name.to_str_res()?.try_into()?;
                Ok(StructType::get_named(ctx, name, None)?.into())
            } else {
                let field_types: Vec<_> = sty
                    .get_field_types_iter()
                    .map(|ty| convert_type(ctx, &ty.as_any_type_enum()))
                    .collect::<Result<_>>()?;
                if let Some(name) = sty.get_name() {
                    let name: Identifier = name.to_str_res()?.try_into()?;
                    Ok(StructType::get_named(ctx, name, Some(field_types))?.into())
                } else {
                    Ok(StructType::get_unnamed(ctx, field_types).into())
                }
            }
        }
        AnyTypeEnum::VectorType(_) => todo!(),
        AnyTypeEnum::VoidType(_) => Ok(VoidType::get(ctx).into()),
    }
}

pub fn convert_ipredicate(ipred: IntPredicate) -> ICmpPredicateAttr {
    match ipred {
        IntPredicate::EQ => ICmpPredicateAttr::EQ,
        IntPredicate::NE => ICmpPredicateAttr::NE,
        IntPredicate::UGT => ICmpPredicateAttr::UGT,
        IntPredicate::UGE => ICmpPredicateAttr::UGE,
        IntPredicate::ULT => ICmpPredicateAttr::ULT,
        IntPredicate::ULE => ICmpPredicateAttr::ULE,
        IntPredicate::SGT => ICmpPredicateAttr::SGT,
        IntPredicate::SGE => ICmpPredicateAttr::SGE,
        IntPredicate::SLT => ICmpPredicateAttr::SLT,
        IntPredicate::SLE => ICmpPredicateAttr::SLE,
    }
}

/// Mapping from inkwell entities to pliron entities.
struct ConversionContext<'ctx> {
    // A map from inkwell's Values to pliron's Values.
    value_map: FxHashMap<AnyValueEnum<'ctx>, Value>,
    // A map from inkwell's basic blocks to plirons'.
    block_map: FxHashMap<IWBasicBlock<'ctx>, Ptr<BasicBlock>>,
    // Entry block of the function we're processing.
    entry_block: Ptr<BasicBlock>,
}

impl<'ctx> ConversionContext<'ctx> {
    fn new(entry_block: Ptr<BasicBlock>) -> Self {
        Self {
            value_map: FxHashMap::default(),
            block_map: FxHashMap::default(),
            entry_block,
        }
    }
}

/// Get the successors of an inkwell block.
fn successors(block: IWBasicBlock) -> Vec<IWBasicBlock> {
    let Some(term) = block.get_terminator() else {
        return vec![];
    };
    match term.get_opcode() {
        InstructionOpcode::Br => {
            if term.get_num_operands() == 1 {
                // Conditional branch
                vec![term
                    .get_operand(0)
                    .unwrap()
                    .expect_right("Branch must have BasicBlock operand")]
            } else {
                assert!(term.get_num_operands() == 3);
                vec![
                    term.get_operand(1)
                        .unwrap()
                        .expect_right("Branch must have BasicBlock operand"),
                    term.get_operand(2)
                        .unwrap()
                        .expect_right("Branch must have BasicBlock operand"),
                ]
            }
        }
        _ => vec![],
    }
}

/// Return RPO ordering of blocks in an inkwell function.
fn rpo(function: FunctionValue) -> Vec<IWBasicBlock> {
    let on_stack = &mut FxHashSet::<IWBasicBlock>::default();
    let mut po = Vec::<IWBasicBlock>::new();

    fn walk<'a>(
        block: IWBasicBlock<'a>,
        on_stack: &mut FxHashSet<IWBasicBlock<'a>>,
        po: &mut Vec<IWBasicBlock<'a>>,
    ) {
        if !on_stack.insert(block) {
            // block already visited.
            return;
        }
        // Visit successors before visiting self.
        for succ in successors(block).into_iter() {
            walk(succ, on_stack, po);
        }
        // Visit self.
        po.push(block);
    }

    // Walk every block (not just entry) since we may have unreachable blocks.
    for block in function.get_basic_block_iter() {
        walk(block, on_stack, &mut po);
    }

    // RPO is the reverse of PO.
    po.reverse();
    po
}

#[derive(Error, Debug)]
pub enum ConversionErr {
    #[error("Unable to get operand with idx {0}")]
    OpdMissing(usize),
    #[error("PHI node must have argument from predecessor block {0}")]
    PhiArgMissing(String),
    #[error("Definition for value {0} not seen yet")]
    UndefinedValue(String),
    #[error("Block definition {0} not seen yet")]
    UndefinedBlock(String),
}

/// Checks if a constant has been processed already, and if not
/// converts it and puts it in the [ConversionContext::value_map].
fn process_constant<'ctx>(
    ctx: &mut Context,
    cctx: &mut ConversionContext<'ctx>,
    val: BasicValueEnum<'ctx>,
) -> Result<()> {
    let any_val = val.as_any_value_enum();
    if cctx.value_map.contains_key(&any_val) {
        return Ok(());
    }
    match val {
        BasicValueEnum::ArrayValue(av) if av.is_const() => todo!(),
        BasicValueEnum::IntValue(iv) if iv.is_constant_int() => {
            // TODO: Zero extend or sign extend?
            let u64 = iv.get_zero_extended_constant().unwrap();
            let int_ty = TypePtr::<IntegerType>::from_ptr(
                convert_type(ctx, &iv.get_type().as_any_type_enum())?,
                ctx,
            )?;
            let val_attr = IntegerAttr::new(int_ty, ApInt::from_u64(u64));
            let const_op = ConstantOp::new(ctx, Box::new(val_attr));
            // Insert at the beginning of the entry block.
            const_op
                .get_operation()
                .insert_at_front(cctx.entry_block, ctx);
            cctx.value_map.insert(any_val, const_op.get_result(ctx));
        }
        BasicValueEnum::IntValue(iv) if iv.is_undef() => {
            let int_ty = convert_type(ctx, &iv.get_type().as_any_type_enum())?;
            let undef_op = UndefOp::new(ctx, int_ty);
            // Insert at the beginning of the entry block.
            undef_op
                .get_operation()
                .insert_at_front(cctx.entry_block, ctx);
            cctx.value_map.insert(any_val, undef_op.get_result(ctx));
        }
        BasicValueEnum::FloatValue(fv) if fv.is_const() => todo!(),
        BasicValueEnum::PointerValue(pv) if pv.is_const() => todo!(),
        BasicValueEnum::StructValue(_sv) => todo!(),
        BasicValueEnum::VectorValue(vv) if vv.is_const() => todo!(),
        _ => (),
    }
    Ok(())
}

fn convert_operands<'ctx>(
    ctx: &mut Context,
    cctx: &mut ConversionContext<'ctx>,
    inst: InstructionValue<'ctx>,
) -> Result<(Vec<Value>, Vec<Ptr<BasicBlock>>)> {
    let mut opds = vec![];
    let mut succs = vec![];
    for opd in inst.get_operands().flatten() {
        if let Some(val) = opd.left() {
            process_constant(ctx, cctx, val)?;
            if let Some(m_val) = cctx.value_map.get(&val.as_any_value_enum()) {
                opds.push(*m_val);
            } else {
                return input_err_noloc!(ConversionErr::UndefinedValue(
                    val.as_any_value_enum().print_to_string().to_string()
                ));
            }
        } else {
            let block = opd.right().unwrap();
            let Some(m_block) = cctx.block_map.get(&block) else {
                return input_err_noloc!(ConversionErr::UndefinedBlock(
                    block.get_name().to_str_res().unwrap().to_string()
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
fn convert_branch_args<'ctx>(
    ctx: &mut Context,
    cctx: &mut ConversionContext<'ctx>,
    src_block: IWBasicBlock<'ctx>,
    dst_block: IWBasicBlock<'ctx>,
) -> Result<Vec<Value>> {
    let mut args = vec![];
    for inst in dst_block.get_instructions() {
        if let Ok(phi) = TryInto::<PhiValue>::try_into(inst) {
            let Some((incoming_val, _)) =
                phi.get_incomings().find(|(_, block)| *block == src_block)
            else {
                return input_err_noloc!(ConversionErr::PhiArgMissing(
                    src_block.get_name().to_str_res().unwrap().to_string()
                ));
            };
            process_constant(ctx, cctx, incoming_val.as_basic_value_enum())?;
            let Some(m_incoming_val) = cctx.value_map.get(&incoming_val.as_any_value_enum()) else {
                return input_err_noloc!(ConversionErr::UndefinedValue(
                    incoming_val
                        .as_any_value_enum()
                        .print_to_string()
                        .to_string()
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

fn convert_instruction<'ctx>(
    ctx: &mut Context,
    cctx: &mut ConversionContext<'ctx>,
    inst: InstructionValue<'ctx>,
) -> Result<Ptr<Operation>> {
    let (ref opds, ref succs) = convert_operands(ctx, cctx, inst)?;
    match inst.get_opcode() {
        InstructionOpcode::Add => {
            let (lhs, rhs) = (get_operand(opds, 0)?, get_operand(opds, 1)?);
            Ok(AddOp::new(ctx, lhs, rhs).get_operation())
        }
        InstructionOpcode::AddrSpaceCast => todo!(),
        InstructionOpcode::Alloca => {
            let elem_type =
                convert_type(ctx, &inst.get_allocated_type().unwrap().as_any_type_enum())?;
            let size = get_operand(opds, 0)?;
            Ok(AllocaOp::new(ctx, elem_type, size).get_operation())
        }
        InstructionOpcode::And => {
            let (lhs, rhs) = (get_operand(opds, 0)?, get_operand(opds, 1)?);
            Ok(AndOp::new(ctx, lhs, rhs).get_operation())
        }
        InstructionOpcode::AShr => {
            let (lhs, rhs) = (get_operand(opds, 0)?, get_operand(opds, 1)?);
            Ok(AShrOp::new(ctx, lhs, rhs).get_operation())
        }
        InstructionOpcode::AtomicCmpXchg => todo!(),
        InstructionOpcode::AtomicRMW => todo!(),
        InstructionOpcode::BitCast => {
            let arg = get_operand(opds, 0)?;
            let res_ty = convert_type(ctx, &inst.get_type())?;
            Ok(BitcastOp::new(ctx, res_ty, arg).get_operation())
        }
        InstructionOpcode::Br => {
            if !opds.is_empty() {
                assert!(
                    succs.len() == 2,
                    "Conditional branch must have two successors"
                );
                let true_dest_opds = convert_branch_args(
                    ctx,
                    cctx,
                    inst.get_parent().unwrap(),
                    inst.get_operand(2).unwrap().unwrap_right(),
                )?;
                let false_dest_opds = convert_branch_args(
                    ctx,
                    cctx,
                    inst.get_parent().unwrap(),
                    inst.get_operand(1).unwrap().unwrap_right(),
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
                    inst.get_parent().unwrap(),
                    inst.get_operand(0).unwrap().unwrap_right(),
                )?;
                Ok(BrOp::new(ctx, get_operand(succs, 0)?, dest_opds).get_operation())
            }
        }
        InstructionOpcode::Call => {
            todo!()
        }
        InstructionOpcode::CallBr => todo!(),
        InstructionOpcode::CatchPad => todo!(),
        InstructionOpcode::CatchRet => todo!(),
        InstructionOpcode::CatchSwitch => todo!(),
        InstructionOpcode::CleanupPad => todo!(),
        InstructionOpcode::CleanupRet => todo!(),
        InstructionOpcode::ExtractElement => todo!(),
        InstructionOpcode::ExtractValue => todo!(),
        InstructionOpcode::FNeg => todo!(),
        InstructionOpcode::FAdd => todo!(),
        InstructionOpcode::FCmp => todo!(),
        InstructionOpcode::FDiv => todo!(),
        InstructionOpcode::Fence => todo!(),
        InstructionOpcode::FMul => todo!(),
        InstructionOpcode::FPExt => todo!(),
        InstructionOpcode::FPToSI => todo!(),
        InstructionOpcode::FPToUI => todo!(),
        InstructionOpcode::FPTrunc => todo!(),
        InstructionOpcode::Freeze => todo!(),
        InstructionOpcode::FRem => todo!(),
        InstructionOpcode::FSub => todo!(),
        InstructionOpcode::GetElementPtr => todo!(),
        InstructionOpcode::ICmp => {
            let pred =
                convert_ipredicate(inst.get_icmp_predicate().expect("ICmp without predicate"));
            Ok(
                ICmpOp::new(ctx, pred, get_operand(opds, 0)?, get_operand(opds, 1)?)
                    .get_operation(),
            )
        }
        InstructionOpcode::IndirectBr => todo!(),
        InstructionOpcode::InsertElement => todo!(),
        InstructionOpcode::InsertValue => todo!(),
        InstructionOpcode::IntToPtr => todo!(),
        InstructionOpcode::Invoke => todo!(),
        InstructionOpcode::LandingPad => todo!(),
        InstructionOpcode::Load => {
            let res_ty = convert_type(ctx, &inst.get_type())?;
            Ok(LoadOp::new(ctx, get_operand(opds, 0)?, res_ty).get_operation())
        }
        InstructionOpcode::LShr => {
            let (lhs, rhs) = (get_operand(opds, 0)?, get_operand(opds, 1)?);
            Ok(LShrOp::new(ctx, lhs, rhs).get_operation())
        }
        InstructionOpcode::Mul => {
            let (lhs, rhs) = (get_operand(opds, 0)?, get_operand(opds, 1)?);
            Ok(MulOp::new(ctx, lhs, rhs).get_operation())
        }
        InstructionOpcode::Or => {
            let (lhs, rhs) = (get_operand(opds, 0)?, get_operand(opds, 1)?);
            Ok(OrOp::new(ctx, lhs, rhs).get_operation())
        }
        InstructionOpcode::Phi => {
            unreachable!("PHI nodes must already be handled")
        }
        InstructionOpcode::PtrToInt => todo!(),
        InstructionOpcode::Resume => todo!(),
        InstructionOpcode::Return => {
            let retval = if inst.get_num_operands() == 1 {
                Some(get_operand(opds, 0)?)
            } else {
                None
            };
            Ok(ReturnOp::new(ctx, retval).get_operation())
        }
        InstructionOpcode::SDiv => {
            let (lhs, rhs) = (get_operand(opds, 0)?, get_operand(opds, 1)?);
            Ok(SDivOp::new(ctx, lhs, rhs).get_operation())
        }
        InstructionOpcode::Select => todo!(),
        InstructionOpcode::SExt => todo!(),
        InstructionOpcode::Shl => {
            let (lhs, rhs) = (get_operand(opds, 0)?, get_operand(opds, 1)?);
            Ok(ShlOp::new(ctx, lhs, rhs).get_operation())
        }
        InstructionOpcode::ShuffleVector => todo!(),
        InstructionOpcode::SIToFP => todo!(),
        InstructionOpcode::SRem => {
            let (lhs, rhs) = (get_operand(opds, 0)?, get_operand(opds, 1)?);
            Ok(SRemOp::new(ctx, lhs, rhs).get_operation())
        }
        InstructionOpcode::Store => {
            let (value_opd, ptr_opd) = (get_operand(opds, 0)?, get_operand(opds, 1)?);
            Ok(StoreOp::new(ctx, value_opd, ptr_opd).get_operation())
        }
        InstructionOpcode::Sub => {
            let (lhs, rhs) = (get_operand(opds, 0)?, get_operand(opds, 1)?);
            Ok(SubOp::new(ctx, lhs, rhs).get_operation())
        }
        InstructionOpcode::Switch => todo!(),
        InstructionOpcode::Trunc => todo!(),
        InstructionOpcode::UDiv => {
            let (lhs, rhs) = (get_operand(opds, 0)?, get_operand(opds, 1)?);
            Ok(UDivOp::new(ctx, lhs, rhs).get_operation())
        }
        InstructionOpcode::UIToFP => todo!(),
        InstructionOpcode::Unreachable => todo!(),
        InstructionOpcode::URem => {
            let (lhs, rhs) = (get_operand(opds, 0)?, get_operand(opds, 1)?);
            Ok(URemOp::new(ctx, lhs, rhs).get_operation())
        }
        InstructionOpcode::UserOp1 => todo!(),
        InstructionOpcode::UserOp2 => todo!(),
        InstructionOpcode::VAArg => todo!(),
        InstructionOpcode::Xor => {
            let (lhs, rhs) = (get_operand(opds, 0)?, get_operand(opds, 1)?);
            Ok(XorOp::new(ctx, lhs, rhs).get_operation())
        }
        InstructionOpcode::ZExt => todo!(),
    }
}

// Convert inkwell `block` to pliron's `m_block`.
fn convert_block<'ctx>(
    ctx: &mut Context,
    cctx: &mut ConversionContext<'ctx>,
    block: IWBasicBlock<'ctx>,
    m_block: Ptr<BasicBlock>,
) -> Result<()> {
    for inst in block.get_instructions() {
        let inst_val = inst.as_any_value_enum();
        if inst.get_opcode() == InstructionOpcode::Phi {
            let ty = convert_type(ctx, &inst.get_type().as_any_type_enum())?;
            let arg_idx = m_block.deref_mut(ctx).add_argument(ty);
            cctx.value_map
                .insert(inst_val, m_block.deref(ctx).get_argument(arg_idx).unwrap());
        } else {
            let m_inst = convert_instruction(ctx, cctx, inst)?;
            m_inst.insert_at_back(m_block, ctx);
            // LLVM instructions have at most one result.
            if let Some(res) = m_inst.deref(ctx).get_result(0) {
                cctx.value_map.insert(inst_val, res);
            }
        }
    }
    Ok(())
}

fn convert_function(ctx: &mut Context, function: FunctionValue) -> Result<FuncOp> {
    let name = function.get_name().to_str_res()?;
    let fn_ty = convert_type(ctx, &function.get_type().as_any_type_enum())?;
    let fn_ty = TypePtr::from_ptr(fn_ty, ctx)?;
    // Create a new FuncOp, which also creates an entry block with the right parameters.
    let m_func = FuncOp::new(ctx, name, fn_ty);
    let m_func_reg = m_func.get_region(ctx);

    let m_entry_block = m_func.get_entry_block(ctx);
    let cctx = &mut ConversionContext::new(m_entry_block);
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
        for (arg_idx, arg) in function.get_param_iter().enumerate() {
            val_map.insert(
                arg.as_any_value_enum(),
                m_entry_block_ref.get_argument(arg_idx).unwrap(),
            );
        }
    }

    // Create, place and map rest of the blocks.
    for block in blocks_iter {
        let label = block.get_name().to_str_res()?.try_into().ok();
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

/// Convert [Module](IWModule) to [ModuleOp].
pub fn convert_module(ctx: &mut Context, module: &IWModule) -> Result<ModuleOp> {
    let module_name = module.get_name().to_str_res()?;
    let m = ModuleOp::new(ctx, module_name);
    // TODO: Convert globals.
    // ...
    // Convert functions.
    for fun in module.get_functions() {
        let m_fun = convert_function(ctx, fun)?;
        m.append_operation(ctx, m_fun.get_operation(), 0);
    }
    Ok(m)
}
