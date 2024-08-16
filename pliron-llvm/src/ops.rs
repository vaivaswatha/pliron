//! [Op]s defined in the LLVM dialect

use pliron::{
    arg_err_noloc,
    attribute::{attr_cast, AttrObj},
    basic_block::BasicBlock,
    builtin::{
        attr_interfaces::TypedAttrInterface,
        attributes::{FloatAttr, IdentifierAttr, IntegerAttr, TypeAttr},
        op_interfaces::{
            BranchOpInterface, CallOpCallable, CallOpInterface, IsTerminatorInterface,
            OneOpdInterface, OneResultInterface, SameOperandsAndResultType, SameOperandsType,
            SameResultsType, ZeroOpdInterface, ZeroResultInterface, ATTR_KEY_CALLEE_TYPE,
        },
        types::{FunctionType, IntegerType, Signedness},
    },
    common_traits::Verify,
    context::{Context, Ptr},
    identifier::Identifier,
    impl_canonical_syntax, impl_op_interface, impl_verify_succ,
    location::Located,
    op::Op,
    operation::Operation,
    parsable::Parsable,
    r#type::{TypeObj, TypePtr},
    result::{Error, ErrorKind, Result},
    utils::vec_exns::VecExtns,
    value::Value,
    verify_err,
};

use crate::{
    op_interfaces::{BinArithOp, IntBinArithOp, IntBinArithOpWithOverflowFlag, PointerTypeResult},
    types::{ArrayType, StructType},
};

use combine::parser::Parser;
use pliron_derive::def_op;
use thiserror::Error;

use super::{
    attributes::{GepIndexAttr, GepIndicesAttr, ICmpPredicateAttr},
    types::PointerType,
};

/// Equivalent to LLVM's return opcode.
///
/// Operands:
///
/// | operand | description |
/// |-----|-------|
/// | `arg` | any type |
#[def_op("llvm.return")]
pub struct ReturnOp;
impl ReturnOp {
    /// Create a new [ReturnOp]
    pub fn new(ctx: &mut Context, value: Option<Value>) -> Self {
        let op = Operation::new(
            ctx,
            Self::get_opid_static(),
            vec![],
            value.into_iter().collect(),
            vec![],
            0,
        );
        ReturnOp { op }
    }

    /// Get the returned value, if it exists.
    pub fn retval(&self, ctx: &Context) -> Option<Value> {
        let op = &*self.get_operation().deref(ctx);
        if op.get_num_operands() == 1 {
            Some(op.get_operand(0))
        } else {
            None
        }
    }
}
impl_canonical_syntax!(ReturnOp);
impl_verify_succ!(ReturnOp);
impl_op_interface!(IsTerminatorInterface for ReturnOp {});

macro_rules! new_int_bin_op {
    (   $(#[$outer:meta])*
        $op_name:ident, $op_id:literal
    ) => {
        #[def_op($op_id)]
        $(#[$outer])*
        /// ### Operands:
        ///
        /// | operand | description |
        /// |-----|-------|
        /// | `lhs` | Signless integer |
        /// | `rhs` | Signless integer |
        ///
        /// ### Result(s):
        ///
        /// | result | description |
        /// |-----|-------|
        /// | `res` | Signless integer |
        pub struct $op_name;

        impl_verify_succ!($op_name);
        impl_canonical_syntax!($op_name);
        impl_op_interface!(OneResultInterface for $op_name {});
        impl_op_interface!(SameOperandsType for $op_name {});
        impl_op_interface!(SameResultsType for $op_name {});
        impl_op_interface!(SameOperandsAndResultType for $op_name {});
        impl_op_interface!(BinArithOp for $op_name {});
        impl_op_interface!(IntBinArithOp for $op_name {});
    }
}

macro_rules! new_int_bin_op_with_overflow {
    (   $(#[$outer:meta])*
        $op_name:ident, $op_id:literal
    ) => {
        new_int_bin_op!(
            $(#[$outer])*
            /// ### Attributes:
            ///
            /// | key | value | via Interface |
            /// |-----|-------| --------------
            /// | [ATTR_KEY_INTEGER_OVERFLOW_FLAGS](super::op_interfaces::ATTR_KEY_INTEGER_OVERFLOW_FLAGS) | [IntegerOverflowFlagsAttr](super::attributes::IntegerOverflowFlagsAttr) | [IntBinArithOpWithOverflowFlag] |
            $op_name,
            $op_id
        );
        impl_op_interface!(IntBinArithOpWithOverflowFlag for $op_name {});
    }
}
new_int_bin_op_with_overflow!(
    /// Equivalent to LLVM's Add opcode.
    AddOp,
    "llvm.add"
);

new_int_bin_op_with_overflow!(
    /// Equivalent to LLVM's Sub opcode.
    SubOp,
    "llvm.sub"
);

new_int_bin_op_with_overflow!(
    /// Equivalent to LLVM's Mul opcode.
    MulOp,
    "llvm.mul"
);

new_int_bin_op_with_overflow!(
    /// Equivalent to LLVM's Shl opcode.
    ShlOp,
    "llvm.shl"
);

new_int_bin_op!(
    /// Equivalent to LLVM's UDiv opcode.
    UDivOp,
    "llvm.udiv"
);

new_int_bin_op!(
    /// Equivalent to LLVM's SDiv opcode.
    SDivOp,
    "llvm.sdiv"
);

new_int_bin_op!(
    /// Equivalent to LLVM's URem opcode.
    URemOp,
    "llvm.urem"
);

new_int_bin_op!(
    /// Equivalent to LLVM's SRem opcode.
    SRemOp,
    "llvm.srem"
);

new_int_bin_op!(
    /// Equivalent to LLVM's And opcode.
    AndOp,
    "llvm.and"
);

new_int_bin_op!(
    /// Equivalent to LLVM's Or opcode.
    OrOp,
    "llvm.or"
);

new_int_bin_op!(
    /// Equivalent to LLVM's Xor opcode.
    XorOp,
    "llvm.xor"
);

new_int_bin_op!(
    /// Equivalent to LLVM's LShr opcode.
    LShrOp,
    "llvm.lshr"
);

new_int_bin_op!(
    /// Equivalent to LLVM's AShr opcode.
    AShrOp,
    "llvm.ashr"
);

#[derive(Error, Debug)]
pub enum ICmpOpVerifyErr {
    #[error("Result must be 1-bit integer (bool)")]
    ResultNotBool,
    #[error("Operand must be integer or pointer types")]
    IncorrectOperandsType,
    #[error("Missing or incorrect predicate attribute")]
    PredAttrErr,
}

/// Equivalent to LLVM's ICmp opcode.
/// ### Operands
/// | operand | description |
/// |-----|-------|
/// | `lhs` | Signless integer or pointer |
/// | `rhs` | Signless integer or pointer |
///
/// ### Result(s):
///
/// | result | description |
/// |-----|-------|
/// | `res` | 1-bit signless integer |
/// ### Attributes:
///
/// | key | value | via Interface |
/// |-----|-------| --------------|
/// | [ATTR_KEY_PREDICATE](icmp_op::ATTR_KEY_PREDICATE) | [ICmpPredicateAttr](ICmpPredicateAttr) | N/A |
#[def_op("llvm.icmp")]
pub struct ICmpOp;

pub mod icmp_op {
    use std::sync::LazyLock;

    use super::*;

    pub static ATTR_KEY_PREDICATE: LazyLock<Identifier> =
        LazyLock::new(|| "llvm_icmp_predicate".try_into().unwrap());
}

impl ICmpOp {
    /// Create a new [ICmpOp]
    pub fn new(ctx: &mut Context, pred: ICmpPredicateAttr, lhs: Value, rhs: Value) -> Self {
        let bool_ty = IntegerType::get(ctx, 1, Signedness::Signless);
        let op = Operation::new(
            ctx,
            Self::get_opid_static(),
            vec![bool_ty.into()],
            vec![lhs, rhs],
            vec![],
            0,
        );
        op.deref_mut(ctx)
            .attributes
            .set(icmp_op::ATTR_KEY_PREDICATE.clone(), pred);
        ICmpOp { op }
    }

    /// Get the predicate
    pub fn predicate(&self, ctx: &Context) -> ICmpPredicateAttr {
        self.get_operation()
            .deref(ctx)
            .attributes
            .get::<ICmpPredicateAttr>(&icmp_op::ATTR_KEY_PREDICATE)
            .unwrap()
            .clone()
    }
}

impl Verify for ICmpOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let loc = self.get_operation().deref(ctx).loc();
        let op = &*self.op.deref(ctx);

        if op
            .attributes
            .get::<ICmpPredicateAttr>(&icmp_op::ATTR_KEY_PREDICATE)
            .is_none()
        {
            verify_err!(op.loc(), ICmpOpVerifyErr::PredAttrErr)?
        }

        let res_ty: TypePtr<IntegerType> =
            TypePtr::from_ptr(self.result_type(ctx), ctx).map_err(|mut err| {
                err.set_loc(loc.clone());
                err
            })?;

        if res_ty.deref(ctx).get_width() != 1 {
            return verify_err!(loc, ICmpOpVerifyErr::ResultNotBool);
        }

        let opd_ty = self.operand_type(ctx).deref(ctx);
        if !(opd_ty.is::<IntegerType>() || opd_ty.is::<PointerType>()) {
            return verify_err!(loc, ICmpOpVerifyErr::IncorrectOperandsType);
        }

        Ok(())
    }
}
impl_canonical_syntax!(ICmpOp);
impl_op_interface!(SameOperandsType for ICmpOp {});
impl_op_interface!(OneResultInterface for ICmpOp {});

#[derive(Error, Debug)]
pub enum AllocaOpVerifyErr {
    #[error("Operand must be a signless integer")]
    OperandType,
    #[error("Missing or incorrect type of attribute for element type")]
    ElemTypeAttr,
}

/// Equivalent to LLVM's Alloca opcode.
/// ### Operands
/// | operand | description |
/// |-----|-------|
/// | `array_size` | Signless integer |
///
/// ### Result(s):
///
/// | result | description |
/// |-----|-------|
/// | `res` | [PointerType] |
///
/// ### Attributes:
///
/// | key | value | via Interface |
/// |-----|-------| --------------|
/// | [ATTR_KEY_ELEM_TYPE](alloca_op::ATTR_KEY_ELEM_TYPE) | [TypeAttr](pliron::builtin::attributes::TypeAttr) | N/A |
#[def_op("llvm.alloca")]
pub struct AllocaOp;
impl_canonical_syntax!(AllocaOp);
impl Verify for AllocaOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let loc = self.get_operation().deref(ctx).loc();
        // Ensure correctness of operand type.
        if !self.operand_type(ctx).deref(ctx).is::<IntegerType>() {
            return verify_err!(loc, AllocaOpVerifyErr::OperandType);
        }
        let op = &*self.op.deref(ctx);
        // Ensure correctness of element type.
        if op
            .attributes
            .get::<TypeAttr>(&alloca_op::ATTR_KEY_ELEM_TYPE)
            .is_none()
        {
            verify_err!(op.loc(), AllocaOpVerifyErr::ElemTypeAttr)?
        }

        Ok(())
    }
}
impl_op_interface!(OneResultInterface for AllocaOp {});
impl_op_interface!(OneOpdInterface for AllocaOp {});
impl_op_interface!(PointerTypeResult for AllocaOp {
    fn result_pointee_type(&self, ctx: &Context) -> Ptr<TypeObj> {
        self.op
        .deref(ctx)
        .attributes
        .get::<TypeAttr>(&alloca_op::ATTR_KEY_ELEM_TYPE)
        .expect("AllocaOp missing or incorrect type for elem_type attribute")
        .get_type()
    }
});

pub mod alloca_op {
    use std::sync::LazyLock;

    use super::*;
    pub static ATTR_KEY_ELEM_TYPE: LazyLock<Identifier> =
        LazyLock::new(|| "llvm_alloca_element_type".try_into().unwrap());
}

impl AllocaOp {
    /// Create a new [AllocaOp]
    pub fn new(ctx: &mut Context, elem_type: Ptr<TypeObj>, size: Value) -> Self {
        let ptr_ty = PointerType::get(ctx).into();
        let op = Operation::new(
            ctx,
            Self::get_opid_static(),
            vec![ptr_ty],
            vec![size],
            vec![],
            0,
        );
        op.deref_mut(ctx).attributes.set(
            alloca_op::ATTR_KEY_ELEM_TYPE.clone(),
            TypeAttr::new(elem_type),
        );
        AllocaOp { op }
    }
}

// Equivalent to LLVM's Bitcast opcode.
/// ### Operands
/// | operand | description |
/// |-----|-------|
/// | `arg` | non-aggregate LLVM type |
///
/// ### Result(s):
///
/// | result | description |
/// |-----|-------|
/// | `res` | non-aggregate LLVM type |
#[def_op("llvm.bitcast")]
pub struct BitcastOp;
impl_canonical_syntax!(BitcastOp);
impl_verify_succ!(BitcastOp);
impl_op_interface!(OneResultInterface for BitcastOp {});
impl_op_interface!(OneOpdInterface for BitcastOp {});

impl BitcastOp {
    /// Create a new [BitcastOp].
    pub fn new(ctx: &mut Context, res_ty: Ptr<TypeObj>, arg: Value) -> Self {
        BitcastOp {
            op: Operation::new(
                ctx,
                Self::get_opid_static(),
                vec![res_ty],
                vec![arg],
                vec![],
                0,
            ),
        }
    }
}

// Equivalent to LLVM's Unconditional Branch.
/// ### Operands
/// | operand | description |
/// |-----|-------|
/// | `dest_opds` | Any number of operands with any LLVM type |
///
/// ### Successors:
///
/// | Successor | description |
/// |-----|-------|
/// | `dest` | Any successor |
#[def_op("llvm.br")]
pub struct BrOp;
impl_canonical_syntax!(BrOp);
impl_verify_succ!(BrOp);
impl_op_interface!(IsTerminatorInterface for BrOp {});
impl_op_interface!(BranchOpInterface for BrOp {
    fn successor_operands(&self, ctx: &Context, succ_idx: usize) -> Vec<Value> {
        assert!(succ_idx == 0, "BrOp has exactly one successor");
        self.get_operation().deref(ctx).operands().collect()
    }
});
impl BrOp {
    /// Create anew [BrOp].
    pub fn new(ctx: &mut Context, dest: Ptr<BasicBlock>, dest_opds: Vec<Value>) -> Self {
        BrOp {
            op: Operation::new(
                ctx,
                Self::get_opid_static(),
                vec![],
                dest_opds,
                vec![dest],
                0,
            ),
        }
    }
}

// Equivalent to LLVM's Conditional Branch.
/// ### Operands
/// | operand | description |
/// |-----|-------|
/// | `condition` | 1-bit signless integer |
/// | `true_dest_opds` | Any number of operands with any LLVM type |
/// | `false_dest_opds` | Any number of operands with any LLVM type |
///
/// ### Successors:
///
/// | Successor | description |
/// |-----|-------|
/// | `true_dest` | Any successor |
/// | `false_dest` | Any successor |
#[def_op("llvm.cond_br")]
pub struct CondBrOp;
impl CondBrOp {
    /// Create anew [CondBrOp].
    pub fn new(
        ctx: &mut Context,
        condition: Value,
        true_dest: Ptr<BasicBlock>,
        mut true_dest_opds: Vec<Value>,
        false_dest: Ptr<BasicBlock>,
        mut false_dest_opds: Vec<Value>,
    ) -> Self {
        let mut operands = vec![condition];
        operands.append(&mut true_dest_opds);
        operands.append(&mut false_dest_opds);
        CondBrOp {
            op: Operation::new(
                ctx,
                Self::get_opid_static(),
                vec![],
                operands,
                vec![true_dest, false_dest],
                0,
            ),
        }
    }

    /// Get the condition value for the branch.
    pub fn condition(&self, ctx: &Context) -> Value {
        self.op.deref(ctx).get_operand(0)
    }
}
impl_canonical_syntax!(CondBrOp);
impl_verify_succ!(CondBrOp);
impl_op_interface!(IsTerminatorInterface for CondBrOp {});
impl_op_interface!(BranchOpInterface for CondBrOp {
    fn successor_operands(&self, ctx: &Context, succ_idx: usize) -> Vec<Value> {
        assert!(succ_idx == 0 || succ_idx == 1, "CondBrOp has exactly two successors");
        let num_opds_succ0 = self.get_operation().deref(ctx).get_successor(0).deref(ctx).get_num_arguments();
        if succ_idx == 0 {
            // Skip `condition` operand and take num_opds_succ0 operands after that.
            self.get_operation().deref(ctx).operands().skip(1).take(num_opds_succ0).collect()
        } else {
            // Skip `condition` and `true_dest_opds`. Take the remaining.
            self.get_operation().deref(ctx).operands().skip(1 + num_opds_succ0).collect()
        }
    }
});

/// A way to express whether a GEP index is a constant or an SSA value
#[derive(Clone)]
pub enum GepIndex {
    Constant(u32),
    Value(Value),
}

#[derive(Error, Debug)]
pub enum GetElementPtrOpErr {
    #[error("GetElementPtrOp has no or incorrect indices attribute")]
    IndicesAttrErr,
    #[error("The indices on this GEP are invalid for its source element type")]
    IndicesErr,
}

// Equivalent to LLVM's GetElementPtr.
/// ### Attributes:
///
/// | key | value | via Interface |
/// |-----|-------| --------------|
/// | [ATTR_KEY_INDICES](gep_op::ATTR_KEY_INDICES) | [GepIndicesAttr](super::attributes::GepIndicesAttr)> | N/A |
/// | [ATTR_KEY_SRC_ELEM_TYPE](gep_op::ATTR_KEY_SRC_ELEM_TYPE) | [TypeAttr] | N/A |
///
/// ### Operands
/// | operand | description |
/// |-----|-------|
/// | `base` | LLVM pointer type |
/// | `dynamicIndices` | Any number of signless integers |
///
/// ### Result(s):
///
/// | result | description |
/// |-----|-------|
/// | `res` | LLVM pointer type |
#[def_op("llvm.gep")]
pub struct GetElementPtrOp;
impl_canonical_syntax!(GetElementPtrOp);
impl_op_interface!(OneResultInterface for GetElementPtrOp {});
impl_op_interface!(PointerTypeResult for GetElementPtrOp {
    fn result_pointee_type(&self, ctx: &Context) -> Ptr<TypeObj> {
        Self::indexed_type(ctx, self.src_elem_type(ctx), &self.indices(ctx)).expect("Invalid indices for GEP")
    }
});
impl Verify for GetElementPtrOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let op = &*self.op.deref(ctx);
        // Ensure that we have the indices as an attribute.
        if op
            .attributes
            .get::<GepIndicesAttr>(&gep_op::ATTR_KEY_INDICES)
            .is_none()
        {
            verify_err!(op.loc(), GetElementPtrOpErr::IndicesAttrErr)?
        }

        if let Err(Error { kind: _, err, loc }) =
            Self::indexed_type(ctx, self.src_elem_type(ctx), &self.indices(ctx))
        {
            return Err(Error {
                kind: ErrorKind::VerificationFailed,
                err,
                loc,
            });
        }

        Ok(())
    }
}

pub mod gep_op {
    use std::sync::LazyLock;

    use super::*;
    /// [Attribute](pliron::attribute::Attribute) to get the indices vector.
    pub static ATTR_KEY_INDICES: LazyLock<Identifier> =
        LazyLock::new(|| "llvm_gep_indices".try_into().unwrap());
    /// [Attribute](pliron::attribute::Attribute) to get the source element type.
    pub static ATTR_KEY_SRC_ELEM_TYPE: LazyLock<Identifier> =
        LazyLock::new(|| "llvm_gep_src_elem_type".try_into().unwrap());
}

impl GetElementPtrOp {
    /// Create a new [GetElementPtrOp]
    pub fn new(
        ctx: &mut Context,
        base: Value,
        indices: Vec<GepIndex>,
        elem_type: TypeAttr,
    ) -> Self {
        let mut attr: Vec<GepIndexAttr> = Vec::new();
        let mut opds: Vec<Value> = vec![base];
        for idx in indices {
            match idx {
                GepIndex::Constant(c) => {
                    attr.push(GepIndexAttr::Constant(c));
                }
                GepIndex::Value(v) => {
                    attr.push(GepIndexAttr::OperandIdx(opds.push_back(v)));
                }
            }
        }
        let op = Operation::new(ctx, Self::get_opid_static(), vec![], opds, vec![], 0);
        op.deref_mut(ctx)
            .attributes
            .set(gep_op::ATTR_KEY_INDICES.clone(), GepIndicesAttr(attr));
        op.deref_mut(ctx)
            .attributes
            .set(gep_op::ATTR_KEY_SRC_ELEM_TYPE.clone(), elem_type);
        GetElementPtrOp { op }
    }

    /// Get the source pointer's element type.
    pub fn src_elem_type(&self, ctx: &Context) -> Ptr<TypeObj> {
        self.op
            .deref(ctx)
            .attributes
            .get::<TypeAttr>(&gep_op::ATTR_KEY_SRC_ELEM_TYPE)
            .expect("GetElementPtrOp missing or has incorrect src_elem_type attribute type")
            .get_type()
    }

    /// Get the base (source) pointer of this GEP.
    pub fn src_ptr(&self, ctx: &Context) -> Value {
        self.get_operation().deref(ctx).get_operand(0)
    }

    /// Get the indices of this GEP.
    pub fn indices(&self, ctx: &Context) -> Vec<GepIndex> {
        let op = &*self.op.deref(ctx);
        op.attributes
            .get::<GepIndicesAttr>(&gep_op::ATTR_KEY_INDICES)
            .unwrap()
            .0
            .iter()
            .map(|index| match index {
                GepIndexAttr::Constant(c) => GepIndex::Constant(*c),
                GepIndexAttr::OperandIdx(i) => GepIndex::Value(op.get_operand(*i)),
            })
            .collect()
    }

    /// Returns the result element type of a GEP with the given source element type and indexes.
    /// See [getIndexedType](https://llvm.org/doxygen/classllvm_1_1GetElementPtrInst.html#a99d4bfe49182f8d80abb1960f2c12d46)
    pub fn indexed_type(
        ctx: &Context,
        src_elem_type: Ptr<TypeObj>,
        indices: &[GepIndex],
    ) -> Result<Ptr<TypeObj>> {
        fn indexed_type_inner(
            ctx: &Context,
            src_elem_type: Ptr<TypeObj>,
            mut idx_itr: impl Iterator<Item = GepIndex>,
        ) -> Result<Ptr<TypeObj>> {
            let Some(idx) = idx_itr.next() else {
                return Ok(src_elem_type);
            };
            let src_elem_type = &*src_elem_type.deref(ctx);
            if let Some(st) = src_elem_type.downcast_ref::<StructType>() {
                let GepIndex::Constant(i) = idx else {
                    return arg_err_noloc!(GetElementPtrOpErr::IndicesErr);
                };
                if st.is_opaque() || i as usize >= st.num_fields() {
                    return arg_err_noloc!(GetElementPtrOpErr::IndicesErr);
                }
                indexed_type_inner(ctx, st.field_type(i as usize), idx_itr)
            } else if let Some(at) = src_elem_type.downcast_ref::<ArrayType>() {
                indexed_type_inner(ctx, at.elem_type(), idx_itr)
            } else {
                arg_err_noloc!(GetElementPtrOpErr::IndicesErr)
            }
        }
        // The first index is for the base (source) pointer. Skip that.
        indexed_type_inner(ctx, src_elem_type, indices.iter().skip(1).cloned())
    }
}

#[derive(Error, Debug)]
pub enum LoadOpVerifyErr {
    #[error("Load operand must be a pointer")]
    OperandTypeErr,
}

/// Equivalent to LLVM's Load opcode.
/// ### Operands
/// | operand | description |
/// |-----|-------|
/// | `addr` | [PointerType] |
///
/// ### Result(s):
///
/// | result | description |
/// |-----|-------|
/// | `res` | sized LLVM type |
///
/// ### Attributes:
///
#[def_op("llvm.load")]
pub struct LoadOp;
impl LoadOp {
    /// Create a new [LoadOp]
    pub fn new(ctx: &mut Context, ptr: Value, res_ty: Ptr<TypeObj>) -> Self {
        LoadOp {
            op: Operation::new(
                ctx,
                Self::get_opid_static(),
                vec![res_ty],
                vec![ptr],
                vec![],
                0,
            ),
        }
    }
}
impl_canonical_syntax!(LoadOp);
impl Verify for LoadOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let loc = self.get_operation().deref(ctx).loc();
        // Ensure correctness of operand type.
        if !self.operand_type(ctx).deref(ctx).is::<PointerType>() {
            return verify_err!(loc, LoadOpVerifyErr::OperandTypeErr);
        }
        Ok(())
    }
}
impl_op_interface!(OneResultInterface for LoadOp {});
impl_op_interface!(OneOpdInterface for LoadOp {});

#[derive(Error, Debug)]
pub enum StoreOpVerifyErr {
    #[error("Store operand must have two operands")]
    NumOpdsErr,
    #[error("Store operand must have a pointer as its second argument")]
    AddrOpdTypeErr,
}

/// Equivalent to LLVM's Store opcode.
/// ### Operands
/// | operand | description |
/// |-----|-------|
/// | `addr` | [PointerType] |
/// | `value` | Sized type |
///
/// ### Attributes:
///
#[def_op("llvm.store")]
pub struct StoreOp;
impl StoreOp {
    /// Create a new [LoadOp]
    pub fn new(ctx: &mut Context, value: Value, ptr: Value) -> Self {
        StoreOp {
            op: Operation::new(
                ctx,
                Self::get_opid_static(),
                vec![],
                vec![value, ptr],
                vec![],
                0,
            ),
        }
    }

    /// Get the value operand
    pub fn value_opd(&self, ctx: &Context) -> Value {
        self.op.deref(ctx).get_operand(0)
    }

    /// Get the address operand
    pub fn address_opd(&self, ctx: &Context) -> Value {
        self.op.deref(ctx).get_operand(1)
    }
}
impl_canonical_syntax!(StoreOp);
impl Verify for StoreOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let loc = self.get_operation().deref(ctx).loc();
        let op = &*self.op.deref(ctx);

        if op.get_num_operands() != 2 {
            return verify_err!(loc, StoreOpVerifyErr::NumOpdsErr);
        }

        use pliron::r#type::Typed;
        // Ensure correctness of the address operand.
        if !op
            .get_operand(1)
            .get_type(ctx)
            .deref(ctx)
            .is::<PointerType>()
        {
            return verify_err!(loc, StoreOpVerifyErr::AddrOpdTypeErr);
        }
        Ok(())
    }
}
impl_op_interface!(ZeroResultInterface for LoadOp {});

/// Equivalent to LLVM's Store opcode.
/// ### Operands
/// | operand | description |
/// |-----|-------|
/// | `callee_operands` | Optional function pointer followed by any number of parameters |
///
////// ### Result(s):
///
/// | result | description |
/// |-----|-------|
/// | `res` | LLVM type |
///
/// ### Attributes:
/// | key | value | via Interface |
/// |-----|-------| --------------|
/// | [ATTR_KEY_CALLEE](call_op::ATTR_KEY_CALLEE) | [IdentifierAttr] | N/A |
/// | [ATTR_KEY_CALLEE_TYPE](pliron::builtin::op_interfaces::ATTR_KEY_CALLEE_TYPE) | [TypeAttr] | [CallOpInterface] |
///
#[def_op("llvm.call")]
pub struct CallOp;

pub mod call_op {
    use std::sync::LazyLock;

    use super::*;
    pub static ATTR_KEY_CALLEE: LazyLock<Identifier> =
        LazyLock::new(|| "llvm_call_callee".try_into().unwrap());
}

impl CallOp {
    /// Get a new [CallOp].
    pub fn new(
        ctx: &mut Context,
        callee: CallOpCallable,
        callee_ty: TypePtr<FunctionType>,
        mut args: Vec<Value>,
    ) -> Self {
        let res_ty = callee_ty.deref(ctx).get_results()[0];
        let op = match callee {
            CallOpCallable::Direct(cval) => {
                let op =
                    Operation::new(ctx, Self::get_opid_static(), vec![res_ty], args, vec![], 0);
                op.deref_mut(ctx)
                    .attributes
                    .set(call_op::ATTR_KEY_CALLEE.clone(), IdentifierAttr::new(cval));
                op
            }
            CallOpCallable::Indirect(csym) => {
                args.insert(0, csym);
                Operation::new(ctx, Self::get_opid_static(), vec![res_ty], args, vec![], 0)
            }
        };
        op.deref_mut(ctx).attributes.set(
            ATTR_KEY_CALLEE_TYPE.clone(),
            TypeAttr::new(callee_ty.into()),
        );
        CallOp { op }
    }
}

impl CallOpInterface for CallOp {
    fn callee(&self, ctx: &Context) -> CallOpCallable {
        let op = self.op.deref(ctx);
        if let Some(callee_sym) = op
            .attributes
            .get::<IdentifierAttr>(&call_op::ATTR_KEY_CALLEE)
        {
            CallOpCallable::Direct(callee_sym.clone().into())
        } else {
            assert!(
                op.get_num_operands() > 0,
                "Indirect call must have function pointer operand"
            );
            CallOpCallable::Indirect(op.get_operand(0))
        }
    }

    fn args(&self, ctx: &Context) -> Vec<Value> {
        let op = self.op.deref(ctx);
        // If this is an indirect call, the first operand is the callee value.
        let skip = if matches!(self.callee(ctx), CallOpCallable::Direct(_)) {
            0
        } else {
            1
        };
        op.operands().skip(skip).collect()
    }
}
impl_canonical_syntax!(CallOp);
impl_verify_succ!(CallOp);
impl_op_interface!(OneResultInterface for CallOp {});

/// Undefined value of a type.
/// See MLIR's [llvm.mlir.undef](https://mlir.llvm.org/docs/Dialects/LLVM/#llvmmlirundef-llvmundefop).
///
/// Results:
///
/// | result | description |
/// |-----|-------|
/// | `result` | any type |
#[def_op("llvm.undef")]
pub struct UndefOp;
impl_canonical_syntax!(UndefOp);
impl_verify_succ!(UndefOp);
impl_op_interface!(OneResultInterface for UndefOp {});

impl UndefOp {
    /// Create a new [UndefOp].
    pub fn new(ctx: &mut Context, result_ty: Ptr<TypeObj>) -> Self {
        let op = Operation::new(
            ctx,
            Self::get_opid_static(),
            vec![result_ty],
            vec![],
            vec![],
            0,
        );
        UndefOp { op }
    }
}

/// Numeric constant.
/// See MLIR's [llvm.mlir.constant](https://mlir.llvm.org/docs/Dialects/LLVM/#llvmmlirconstant-llvmconstantop).
///
/// Attributes:
///
/// | key | value |
/// |-----|-------|
/// |[ATTR_KEY_VALUE](constant_op::ATTR_KEY_VALUE) | [IntegerAttr] or [FloatAttr] |
///
/// Results:
///
/// | result | description |
/// |-----|-------|
/// | `result` | any type |
#[def_op("llvm.constant")]
pub struct ConstantOp;

pub mod constant_op {
    use std::sync::LazyLock;

    use super::*;
    /// Attribute key for the constant value.
    pub static ATTR_KEY_VALUE: LazyLock<Identifier> =
        LazyLock::new(|| "llvm_constant_value".try_into().unwrap());
}

impl ConstantOp {
    /// Get the constant value that this Op defines.
    pub fn get_value(&self, ctx: &Context) -> AttrObj {
        let op = self.get_operation().deref(ctx);
        op.attributes
            .0
            .get(&constant_op::ATTR_KEY_VALUE)
            .unwrap()
            .clone()
    }

    /// Create a new [ConstantOp].
    pub fn new(ctx: &mut Context, value: AttrObj) -> Self {
        let result_type = attr_cast::<dyn TypedAttrInterface>(&*value)
            .expect("ConstantOp const value must provide TypedAttrInterface")
            .get_type();
        let op = Operation::new(
            ctx,
            Self::get_opid_static(),
            vec![result_type],
            vec![],
            vec![],
            0,
        );
        op.deref_mut(ctx)
            .attributes
            .0
            .insert(constant_op::ATTR_KEY_VALUE.clone(), value);
        ConstantOp { op }
    }
}

#[derive(Error, Debug)]
#[error("{}: Unexpected type", ConstantOp::get_opid_static())]
pub struct ConstantOpVerifyErr;

impl Verify for ConstantOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        let loc = self.get_operation().deref(ctx).loc();
        let value = self.get_value(ctx);
        if !(value.is::<IntegerAttr>() || value.is::<FloatAttr>()) {
            return verify_err!(loc, ConstantOpVerifyErr);
        }
        Ok(())
    }
}

impl_canonical_syntax!(ConstantOp);
impl_op_interface! (ZeroOpdInterface for ConstantOp {});
impl_op_interface! (OneResultInterface for ConstantOp {});

/// Register ops in the LLVM dialect.
pub fn register(ctx: &mut Context) {
    AddOp::register(ctx, AddOp::parser_fn);
    SubOp::register(ctx, SubOp::parser_fn);
    MulOp::register(ctx, MulOp::parser_fn);
    ShlOp::register(ctx, ShlOp::parser_fn);
    UDivOp::register(ctx, UDivOp::parser_fn);
    SDivOp::register(ctx, SDivOp::parser_fn);
    URemOp::register(ctx, URemOp::parser_fn);
    SRemOp::register(ctx, SRemOp::parser_fn);
    AndOp::register(ctx, AndOp::parser_fn);
    OrOp::register(ctx, OrOp::parser_fn);
    XorOp::register(ctx, XorOp::parser_fn);
    LShrOp::register(ctx, LShrOp::parser_fn);
    AShrOp::register(ctx, AShrOp::parser_fn);
    ICmpOp::register(ctx, ICmpOp::parser_fn);
    AllocaOp::register(ctx, AllocaOp::parser_fn);
    BitcastOp::register(ctx, BitcastOp::parser_fn);
    BrOp::register(ctx, BrOp::parser_fn);
    CondBrOp::register(ctx, CondBrOp::parser_fn);
    GetElementPtrOp::register(ctx, GetElementPtrOp::parser_fn);
    LoadOp::register(ctx, LoadOp::parser_fn);
    StoreOp::register(ctx, StoreOp::parser_fn);
    CallOp::register(ctx, CallOp::parser_fn);
    ConstantOp::register(ctx, ConstantOp::parser_fn);
    UndefOp::register(ctx, UndefOp::parser_fn);
    ReturnOp::register(ctx, ReturnOp::parser_fn);
}
