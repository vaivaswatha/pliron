//! Implementation of various op interfaces for LLVM IR instructions.

use pliron::{
    basic_block::BasicBlock,
    context::{Context, Ptr},
    derive::op_interface_impl,
    opts::dce::{BlockArgRemoval, SideEffects},
};

use crate::ops::{
    AShrOp, AddOp, AddressOfOp, AllocaOp, AndOp, BitcastOp, ConstantOp, ExtractElementOp,
    ExtractValueOp, FAddOp, FCmpOp, FDivOp, FMulOp, FNegOp, FPExtOp, FPToSIOp, FPToUIOp, FPTruncOp,
    FRemOp, FSubOp, FreezeOp, FuncOp, GetElementPtrOp, ICmpOp, InsertElementOp, InsertValueOp,
    IntToPtrOp, LShrOp, MulOp, OrOp, PoisonOp, PtrToIntOp, SDivOp, SExtOp, SIToFPOp, SRemOp,
    SelectOp, ShlOp, ShuffleVectorOp, SubOp, TruncOp, UDivOp, UIToFPOp, URemOp, UndefOp, XorOp,
    ZExtOp, ZeroOp,
};

// Implement [SideEffects] with `has_side_effects` returning `false`
macro_rules! impl_side_effects_false {
  ($($op:ty),+ $(,)?) => {
    $(
      #[op_interface_impl]
      impl SideEffects for $op {
        fn has_side_effects(&self, _ctx: &Context) -> bool {
          false
        }
      }
    )+
  };
}

// Pure value-producing ops with no memory/control side effects.
// We don't need to implement [SideEffects] for the other ops,
// because the assumption is that the absense of the interface
// implies the presence of side effects, which is a safe default for DCE.
impl_side_effects_false!(
    AddOp,
    SubOp,
    MulOp,
    ShlOp,
    UDivOp,
    SDivOp,
    URemOp,
    SRemOp,
    AndOp,
    OrOp,
    XorOp,
    LShrOp,
    AShrOp,
    ICmpOp,
    AllocaOp,
    BitcastOp,
    IntToPtrOp,
    PtrToIntOp,
    UndefOp,
    PoisonOp,
    FreezeOp,
    ConstantOp,
    ZeroOp,
    AddressOfOp,
    SExtOp,
    ZExtOp,
    FPExtOp,
    TruncOp,
    FPTruncOp,
    FPToSIOp,
    FPToUIOp,
    SIToFPOp,
    UIToFPOp,
    InsertValueOp,
    ExtractValueOp,
    InsertElementOp,
    ExtractElementOp,
    ShuffleVectorOp,
    SelectOp,
    FNegOp,
    FAddOp,
    FSubOp,
    FMulOp,
    FDivOp,
    FRemOp,
    FCmpOp,
    GetElementPtrOp,
);

#[op_interface_impl]
impl BlockArgRemoval for FuncOp {
    fn can_remove_block_args(&self, ctx: &Context, block: Ptr<BasicBlock>) -> bool {
        !matches!(self.get_entry_block(ctx), Some(entry) if entry == block)
    }
}
