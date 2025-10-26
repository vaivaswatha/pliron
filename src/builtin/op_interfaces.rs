use std::collections::hash_map;

use pliron::derive::op_interface;
use rustc_hash::FxHashMap;
use thiserror::Error;

use crate::{
    basic_block::BasicBlock,
    builtin::{
        attributes::{OperandSegmentSizesAttr, TypeAttr},
        type_interfaces::FunctionTypeInterface,
    },
    context::{Context, Ptr},
    dict_key,
    graph::walkers::interruptible::{WalkResult, walk_advance, walk_break},
    identifier::Identifier,
    linked_list::ContainsLinkedList,
    location::{Located, Location},
    op::{Op, op_cast},
    operation::Operation,
    printable::Printable,
    region::Region,
    result::Result,
    symbol_table::{SymbolTableCollection, walk_symbol_table},
    r#type::{TypeObj, Typed, type_impls},
    value::Value,
    verify_err, verify_error,
};

use super::attributes::IdentifierAttr;

/// An [Op] implementing this interface is a block terminator.
#[op_interface]
pub trait IsTerminatorInterface {
    fn verify(_op: &dyn Op, _ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        Ok(())
    }
}

#[derive(Error, Debug)]
pub enum BranchOpInterfaceVerifyErr {
    #[error("Branch Op is passing {provided} arguments, but target block expects {expected}")]
    SuccessorOperandsMismatch { provided: usize, expected: usize },
    #[error("Forwarded operand at {idx} is of type {forwarded}, but should've been {expected}")]
    SuccessorOperandTypeMismatch {
        idx: usize,
        forwarded: String,
        expected: String,
    },
}

/// This [terminator](IsTerminatorInterface) [Op] branches to
/// other [BasicBlock]s, possibly passing arguments to the target block.
///
/// This is similar to MLIR's
/// [BranchOpInterface](https://github.com/llvm/llvm-project/blob/b1f04d57f5818914d7db506985e2932f217844bd/mlir/include/mlir/Interfaces/ControlFlowInterfaces.td)
/// but is stricter: (1) Produced operands aren't supported, just forwarded.
/// (2) Type of the value passed is expected to be the same as the target block argument.
#[op_interface]
pub trait BranchOpInterface: IsTerminatorInterface {
    /// Get a list of [Value]s that are forwarded to the target block.
    fn successor_operands(&self, ctx: &Context, succ_idx: usize) -> Vec<Value>;

    fn verify(op: &dyn Op, ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        let self_op = op_cast::<dyn BranchOpInterface>(op).unwrap();
        // Verify that the values passed to a target block
        // matches the arguments of that block.
        for (succ_idx, succ) in op.get_operation().deref(ctx).successors().enumerate() {
            let succ = &*succ.deref(ctx);
            let operands = self_op.successor_operands(ctx, succ_idx);
            if succ.get_num_arguments() != operands.len() {
                return verify_err!(
                    op.loc(ctx),
                    BranchOpInterfaceVerifyErr::SuccessorOperandsMismatch {
                        provided: operands.len(),
                        expected: succ.get_num_arguments()
                    }
                );
            }
            for (idx, operand) in operands.iter().enumerate() {
                let block_arg = succ.get_argument(idx);
                if operand.get_type(ctx) != block_arg.get_type(ctx) {
                    return verify_err!(
                        op.loc(ctx),
                        BranchOpInterfaceVerifyErr::SuccessorOperandTypeMismatch {
                            idx,
                            forwarded: operand.get_type(ctx).disp(ctx).to_string(),
                            expected: block_arg.get_type(ctx).disp(ctx).to_string(),
                        }
                    );
                }
            }
        }
        Ok(())
    }
}

dict_key!(
    /// Key for the `operand_segment_sizes` attribute.
    ATTR_KEY_OPERAND_SEGMENT_SIZES, "operand_segment_sizes"
);

#[derive(Error, Debug)]
/// Error returned when verifying an [OperandSegmentInterface] operation
pub enum OperandSegmentInterfaceVerifyErr {
    #[error("operand_segment_sizes attribute not found")]
    OperandSegmentSizesAttrErr,
    #[error("operand_segment_sizes total {0} does not match the number of operands {1}")]
    OperandSegmentSizesTotalMismatchErr(u32, u32),
}

/// In the case of variadic operands, sometimes it makes sense to group
/// contiguous operands together into a segment. This interface aids doing that.
/// MLIR achieves this by having ODS (tablegen)' `AttrSizedOperandSegments` generate
/// `getODSOperands()` based on the `operandSegmentSizes` attribute.
///
/// ### Attribute(s):
/// | Name | Static Name Identifier | Type |
/// |------|------------------------| -----|
/// | operand_segment_sizes | [ATTR_KEY_OPERAND_SEGMENT_SIZES] | [OperandSegmentSizesAttr](crate::builtin::attributes::OperandSegmentSizesAttr) |
#[op_interface]
pub trait OperandSegmentInterface {
    /// Given a list of segmented operands, compute the segment sizes and flatten the operands
    /// (ready for use in constructing an operation).
    /// Call `set_operand_segment_sizes` with the computed segment sizes to set the attribute.
    fn compute_segment_sizes(operands: Vec<Vec<Value>>) -> (Vec<Value>, OperandSegmentSizesAttr)
    where
        Self: Sized,
    {
        let sizes = operands
            .iter()
            .map(|seg| seg.len().try_into().unwrap())
            .collect::<Vec<_>>();
        let flat_operands = operands.into_iter().flatten().collect();

        let sizes_attr = OperandSegmentSizesAttr(sizes);
        (flat_operands, sizes_attr)
    }

    /// Get the `idx`th segment of operands.
    fn get_segment(&self, ctx: &Context, idx: usize) -> Vec<Value> {
        let self_op = self.get_operation().deref(ctx);
        let sizes_attr = self_op
            .attributes
            .get::<OperandSegmentSizesAttr>(&ATTR_KEY_OPERAND_SEGMENT_SIZES)
            .unwrap();
        let sizes = &sizes_attr.0;

        if idx >= sizes.len() {
            return vec![];
        }

        let start = sizes[..idx].iter().sum::<u32>() as usize;
        let len = sizes[idx] as usize;

        self_op.operands().skip(start).take(len).collect()
    }

    /// Set the `operand_segment_sizes` attribute for this operation.
    fn set_operand_segment_sizes(&self, ctx: &Context, sizes: OperandSegmentSizesAttr) {
        let mut self_op = self.get_operation().deref_mut(ctx);
        self_op
            .attributes
            .set(ATTR_KEY_OPERAND_SEGMENT_SIZES.clone(), sizes);
    }

    fn verify(op: &dyn Op, ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        let self_op = op.get_operation().deref(ctx);
        let Some(attr) = self_op
            .attributes
            .get::<OperandSegmentSizesAttr>(&ATTR_KEY_OPERAND_SEGMENT_SIZES)
        else {
            return verify_err!(
                self_op.loc(),
                OperandSegmentInterfaceVerifyErr::OperandSegmentSizesAttrErr
            );
        };

        let total = attr.0.iter().cloned().sum::<u32>();

        let num_operands: u32 = self_op.get_num_operands().try_into().unwrap();
        if total != num_operands {
            return verify_err!(
                self_op.loc(),
                OperandSegmentInterfaceVerifyErr::OperandSegmentSizesTotalMismatchErr(
                    total,
                    num_operands
                )
            );
        }

        Ok(())
    }
}

/// Describe the abstract semantics of [Regions](crate::region::Region).
///
/// See MLIR's [RegionKind](https://mlir.llvm.org/docs/Interfaces/#regionkindinterfaces).
pub enum RegionKind {
    /// Represents a graph region without control flow semantics.
    Graph,
    /// Represents an [SSA-style control](https://mlir.llvm.org/docs/LangRef/#control-flow-and-ssacfg-regions)
    /// flow region with basic blocks and reachability.
    SSACFG,
}

/// Info on contained [Regions](crate::region::Region).
#[op_interface]
pub trait RegionKindInterface {
    /// Return the kind of the region with the given index inside this operation.
    fn get_region_kind(&self, idx: usize) -> RegionKind;
    /// Return true if the region with the given index inside this operation
    /// must require dominance to hold.
    fn has_ssa_dominance(&self, idx: usize) -> bool;

    fn verify(_op: &dyn Op, _ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        Ok(())
    }
}

#[derive(Error, Debug)]
#[error("Op {0} must have a single region")]
pub struct OneRegionVerifyErr(String);

/// [Op]s that have exactly one region.
#[op_interface]
pub trait OneRegionInterface {
    /// Get the single region that this [Op] has.
    fn get_region(&self, ctx: &Context) -> Ptr<Region> {
        self.get_operation().deref(ctx).get_region(0)
    }

    /// Checks that the operation has exactly one region.
    fn verify(op: &dyn Op, ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        let self_op = op.get_operation().deref(ctx);
        if self_op.regions.len() != 1 {
            return verify_err!(self_op.loc(), OneRegionVerifyErr(op.get_opid().to_string()));
        }
        Ok(())
    }
}

#[derive(Error, Debug)]
#[error("Op {0} must have at most one region")]
pub struct AtMostOneRegionVerifyErr(String);

/// [Op]s that have at most one region.
#[op_interface]
pub trait AtMostOneRegionInterface {
    fn verify(op: &dyn Op, ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        let self_op = op.get_operation().deref(ctx);
        if self_op.regions.len() > 1 {
            return verify_err!(
                self_op.loc(),
                AtMostOneRegionVerifyErr(op.get_opid().to_string())
            );
        }
        Ok(())
    }

    fn get_region(&self, ctx: &Context) -> Option<Ptr<Region>> {
        let self_op = self.get_operation().deref(ctx);
        self_op.regions().next()
    }
}

#[derive(Error, Debug)]
#[error("Op {0} must only have regions with single block")]
pub struct SingleBlockRegionVerifyErr(String);

/// [Op]s with regions that have a single block.
#[op_interface]
pub trait SingleBlockRegionInterface {
    /// Get the single body block in `region_idx`.
    fn get_body(&self, ctx: &Context, region_idx: usize) -> Ptr<BasicBlock> {
        self.get_operation()
            .deref(ctx)
            .get_region(region_idx)
            .deref(ctx)
            .get_head()
            .expect("Expected SingleBlockRegion Op to contain a block")
    }

    /// Insert an operation at the end of the single block in `region_idx`.
    fn append_operation(&self, ctx: &mut Context, op: Ptr<Operation>, region_idx: usize) {
        op.insert_at_back(self.get_body(ctx, region_idx), ctx);
    }

    /// Checks that the operation has regions with single block.
    fn verify(op: &dyn Op, ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        let self_op = op.get_operation().deref(ctx);
        for region in &self_op.regions {
            if region.deref(ctx).iter(ctx).count() != 1 {
                return verify_err!(
                    self_op.loc(),
                    SingleBlockRegionVerifyErr(self_op.get_opid().to_string())
                );
            }
        }
        Ok(())
    }
}

/// [Op]s whose single-basic-block regions need not have a terminator.
#[op_interface]
pub trait NoTerminatorInterface: SingleBlockRegionInterface {
    fn verify(_op: &dyn Op, _ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        Ok(())
    }
}

dict_key!(
    /// Key for symbol name attribute when the operation defines a symbol.
    ATTR_KEY_SYM_NAME, "sym_name"
);

#[derive(Error, Debug)]
#[error("Op implementing SymbolOpInterface does not have a symbol defined")]
pub struct SymbolOpInterfaceErr;

/// [Op] that defines or declares a [symbol](https://mlir.llvm.org/docs/SymbolsAndSymbolTables/#symbol).
///
/// ### Attribute(s):
/// | Name | Static Name Identifier | Type |
/// |------|------------------------| -----|
/// | sym_name | [ATTR_KEY_SYM_NAME] | [IdentifierAttr](crate::builtin::attributes::IdentifierAttr) |
#[op_interface]
pub trait SymbolOpInterface {
    /// Get the name of the symbol defined by this operation.
    fn get_symbol_name(&self, ctx: &Context) -> Identifier {
        let self_op = self.get_operation().deref(ctx);
        let s_attr = self_op
            .attributes
            .get::<IdentifierAttr>(&ATTR_KEY_SYM_NAME)
            .unwrap();
        s_attr.clone().into()
    }

    /// Set a name for the symbol defined by this operation.
    fn set_symbol_name(&self, ctx: &mut Context, name: Identifier) {
        let name_attr = IdentifierAttr::new(name);
        let mut self_op = self.get_operation().deref_mut(ctx);
        self_op.attributes.set(ATTR_KEY_SYM_NAME.clone(), name_attr);
    }

    fn verify(op: &dyn Op, ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        let self_op = op.get_operation().deref(ctx);
        if self_op
            .attributes
            .get::<IdentifierAttr>(&ATTR_KEY_SYM_NAME)
            .is_none()
        {
            return verify_err!(op.loc(ctx), SymbolOpInterfaceErr);
        }
        Ok(())
    }
}

#[derive(Error, Debug)]
pub enum SymbolTableInterfaceErr {
    #[error("Multiple definitions of Symbol {0}")]
    SymbolRedefined(String),
}

// Any [Op] that holds a symbol table.
#[op_interface]
pub trait SymbolTableInterface: SingleBlockRegionInterface + OneRegionInterface {
    /// Lookup a symbol in this symbol table op. Linear search.
    fn lookup(&self, ctx: &Context, sym: &Identifier) -> Option<Ptr<Operation>> {
        for op in self.get_body(ctx, 0).deref(ctx).iter(ctx) {
            if let Some(sym_op) = op_cast::<dyn SymbolOpInterface>(&*Operation::get_op(op, ctx))
                && &sym_op.get_symbol_name(ctx) == sym
            {
                return Some(op);
            }
        }
        None
    }

    fn verify(op: &dyn Op, ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        let op = op_cast::<dyn SymbolTableInterface>(op).unwrap();

        // Check that every symbol is defined only once.
        let mut seen = FxHashMap::<Identifier, Location>::default();
        let table_ops_block = op.get_body(ctx, 0);
        for op in table_ops_block.deref(ctx).iter(ctx) {
            if let Some(sym_op) = op_cast::<dyn SymbolOpInterface>(&*Operation::get_op(op, ctx)) {
                let sym = sym_op.get_symbol_name(ctx);
                match seen.entry(sym.clone()) {
                    hash_map::Entry::Occupied(prev_loc) => {
                        return verify_err!(
                            op.deref(ctx).loc(),
                            verify_error!(
                                prev_loc.get().clone(),
                                SymbolTableInterfaceErr::SymbolRedefined(sym.to_string())
                            )
                        );
                    }
                    hash_map::Entry::Vacant(vac) => {
                        vac.insert(op.deref(ctx).loc());
                    }
                }
            }
        }

        struct State {
            symbol_table_collection: SymbolTableCollection,
            res: Result<()>,
        }
        // Verify Ops inside that implement [SymbolUserOpInterface].
        fn callback(ctx: &Context, state: &mut State, op: Ptr<Operation>) -> WalkResult<()> {
            if let Some(sym_user_op) =
                op_cast::<dyn SymbolUserOpInterface>(&*Operation::get_op(op, ctx))
                && let Err(err) =
                    sym_user_op.verify_symbol_uses(ctx, &mut state.symbol_table_collection)
            {
                state.res = Err(err);
                return walk_break(());
            }
            walk_advance()
        }

        let mut state = State {
            symbol_table_collection: SymbolTableCollection::new(),
            res: Ok(()),
        };
        walk_symbol_table(dyn_clone::clone_box(op), ctx, &mut state, callback);
        state.res
    }
}

#[op_interface]
pub trait SymbolUserOpInterface {
    /// Verify the symbol uses held by this operation. This is called when verifying
    /// a symbol table operation that (possibly transitively) contains this operation.
    fn verify_symbol_uses(
        &self,
        ctx: &Context,
        symbol_tables: &mut SymbolTableCollection,
    ) -> Result<()>;

    /// Returns the list of symbols used by this operation.
    fn used_symbols(&self, ctx: &Context) -> Vec<Identifier>;

    /// Nothing (by default) to verify for symbol users. Override if needed.
    fn verify(_op: &dyn Op, _ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        Ok(())
    }
}

#[derive(Error, Debug)]
#[error("Op {0} must have single result")]
pub struct OneResultVerifyErr(pub String);

/// An [Op] having exactly one result.
#[op_interface]
pub trait OneResultInterface {
    /// Get the single result defined by this [Op].
    fn get_result(&self, ctx: &Context) -> Value {
        self.get_operation().deref(ctx).get_result(0)
    }

    /// Get the type of the single result defined by this [Op].
    fn result_type(&self, ctx: &Context) -> Ptr<TypeObj> {
        self.get_operation().deref(ctx).get_type(0)
    }

    fn verify(op: &dyn Op, ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        let op = &*op.get_operation().deref(ctx);
        if op.get_num_results() != 1 {
            return verify_err!(op.loc(), OneResultVerifyErr(op.get_opid().to_string()));
        }
        Ok(())
    }
}

#[derive(Error, Debug)]
#[error("Op {0} must not produce result(s)")]
pub struct ZeroResultVerifyErr(pub String);

/// An [Op] having no results.
#[op_interface]
pub trait ZeroResultInterface {
    fn verify(op: &dyn Op, ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        let op = &*op.get_operation().deref(ctx);
        if op.get_num_results() != 0 {
            return verify_err!(op.loc(), ZeroResultVerifyErr(op.get_opid().to_string()));
        }
        Ok(())
    }
}

#[derive(Error, Debug)]
#[error("Op {0} must not have any operand")]
pub struct ZeroOpdVerifyErr(String);

/// An [Op] having no operands.
#[op_interface]
pub trait ZeroOpdInterface {
    fn verify(op: &dyn Op, ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        let op = &*op.get_operation().deref(ctx);
        if op.get_num_operands() != 0 {
            return verify_err!(op.loc(), ZeroOpdVerifyErr(op.get_opid().to_string()));
        }
        Ok(())
    }
}

#[derive(Error, Debug)]
#[error("Op must have exactly one operand")]
pub struct OneOpdVerifyErr(String);

/// An [Op] having no operands.
#[op_interface]
pub trait OneOpdInterface {
    /// Get the single operand used by this [Op].
    fn get_operand(&self, ctx: &Context) -> Value {
        self.get_operation().deref(ctx).get_operand(0)
    }

    /// Get the type of the single operand used by this [Op].
    fn operand_type(&self, ctx: &Context) -> Ptr<TypeObj> {
        self.get_operand(ctx).get_type(ctx)
    }

    fn verify(op: &dyn Op, ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        let op = &*op.get_operation().deref(ctx);
        if op.get_num_operands() != 1 {
            return verify_err!(op.loc(), OneOpdVerifyErr(op.get_opid().to_string()));
        }
        Ok(())
    }
}

/// An [Op] whose regions's SSA names are isolated from above.
/// This is similar to (but not the same as) MLIR's
/// [IsolatedFromAbove](https://mlir.llvm.org/docs/Traits/#isolatedfromabove) trait.
/// Definition: all regions that are reachable / traversible in any
/// direction in the region hierarchy without passing an `IsolatedFromAbove`
/// barrier, share the same SSA name space.
/// i.e., a region that is not `IsolatedFromAbove` cannot have any SSA name
/// in common with that of any of its ancestors or siblings or cousins etc.
#[op_interface]
pub trait IsolatedFromAboveInterface {
    fn verify(_op: &dyn Op, _ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        Ok(())
    }
}

#[derive(Error, Debug)]
pub enum SameOperandsTypeVerifyErr {
    #[error("Op with same operands types must have at least one operand")]
    NoOperands,
    #[error("Op has different operand types")]
    TypesDiffer,
}

/// An [Op] with at least one operand, and them all having the same type.
#[op_interface]
pub trait SameOperandsType {
    /// Get the common type of the operands.
    fn operand_type(&self, ctx: &Context) -> Ptr<TypeObj> {
        self.get_operation().deref(ctx).get_operand(0).get_type(ctx)
    }

    fn verify(op: &dyn Op, ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        let op = op.get_operation().deref(ctx);

        if op.get_num_operands() == 0 {
            return verify_err!(op.loc(), SameOperandsTypeVerifyErr::NoOperands);
        }

        let mut opds = op.operands();
        let ty = opds.next().unwrap().get_type(ctx);
        for opd in opds {
            if opd.get_type(ctx) != ty {
                return verify_err!(op.loc(), SameResultsTypeVerifyErr::TypesDiffer);
            }
        }

        Ok(())
    }
}

#[derive(Error, Debug)]
pub enum SameResultsTypeVerifyErr {
    #[error("Op with same result types must have at least one result")]
    NoResults,
    #[error("Op has different result types")]
    TypesDiffer,
}

// An [Op] with at least one result, and them all having the same type.
#[op_interface]
pub trait SameResultsType {
    /// Get the common type of the results.
    fn result_type(&self, ctx: &Context) -> Ptr<TypeObj> {
        self.get_operation().deref(ctx).get_result(0).get_type(ctx)
    }

    fn verify(op: &dyn Op, ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        let op = op.get_operation().deref(ctx);

        if op.get_num_results() == 0 {
            return verify_err!(op.loc(), SameResultsTypeVerifyErr::NoResults);
        }

        let mut results = op.results();
        let ty = results.next().unwrap().get_type(ctx);
        for res in results {
            if res.get_type(ctx) != ty {
                return verify_err!(op.loc(), SameResultsTypeVerifyErr::TypesDiffer);
            }
        }
        Ok(())
    }
}

#[derive(Error, Debug)]
#[error("Op has different operand and result types")]
pub struct SameOperandsAndResultTypeVerifyErr;

/// An [Op] with at least one result and one operand, and them all having the same type.
/// See MLIR's [SameOperandsAndResultType](https://mlir.llvm.org/doxygen/classmlir_1_1OpTrait_1_1SameOperandsAndResultType.html).
#[op_interface]
pub trait SameOperandsAndResultType: SameOperandsType + SameResultsType {
    /// Get the common type of results / operands.
    fn get_type(&self, ctx: &Context) -> Ptr<TypeObj> {
        self.result_type(ctx)
    }

    fn verify(op: &dyn Op, ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        let res_ty = op_cast::<dyn SameResultsType>(op)
            .expect("Op must impl SameResultsType")
            .result_type(ctx);
        let opd_ty = op_cast::<dyn SameOperandsType>(op)
            .expect("Op must impl SameOperandsType")
            .operand_type(ctx);

        if res_ty != opd_ty {
            return verify_err!(op.loc(ctx), SameOperandsAndResultTypeVerifyErr);
        }

        Ok(())
    }
}

/// A callable object is either a
///   - direct callee, expressed as a symbol)
///   - indirect callee, a [Value] pointing to the function to be called.
#[derive(Clone)]
pub enum CallOpCallable {
    Direct(Identifier),
    Indirect(Value),
}

#[derive(Error, Debug)]
pub enum CallOpInterfaceErr {
    #[error("Callee type attribute not found")]
    CalleeTypeAttrNotFoundErr,
    #[error("Callee type attribute must impl FunctionTypeInterface")]
    CalleeTypeAttrIncorrectTypeErr,
}

dict_key!(ATTR_KEY_CALLEE_TYPE, "callee_type");

/// A call-like op: Transfers control from one function to another.
/// See MLIR's [CallOpInterface](https://mlir.llvm.org/docs/Interfaces/#callinterfaces).
///
/// ### Attribute(s):
///
/// | Name | Static Name Identifier | Type |
/// |------|------------------------| -----|
/// | callee_type | [ATTR_KEY_CALLEE_TYPE] | [TypeAttr](crate::builtin::attributes::TypeAttr) |
#[op_interface]
pub trait CallOpInterface {
    fn verify(op: &dyn Op, ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        let op = op.get_operation().deref(ctx);
        let Some(callee_type_attr) = op.attributes.get::<TypeAttr>(&ATTR_KEY_CALLEE_TYPE) else {
            return verify_err!(op.loc(), CallOpInterfaceErr::CalleeTypeAttrNotFoundErr);
        };
        if !type_impls::<dyn FunctionTypeInterface>(&**callee_type_attr.get_type(ctx).deref(ctx)) {
            return verify_err!(op.loc(), CallOpInterfaceErr::CalleeTypeAttrIncorrectTypeErr);
        }
        Ok(())
    }

    /// Get the function that this call op is calling
    ///   - A symbol if this is a direct call
    ///   - A value if this is an indirect call
    fn callee(&self, ctx: &Context) -> CallOpCallable;

    /// Get arguments passed to callee
    fn args(&self, ctx: &Context) -> Vec<Value>;

    /// Type of the callee
    fn callee_type(&self, ctx: &Context) -> Ptr<TypeObj> {
        let self_op = self.get_operation().deref(ctx);
        self_op
            .attributes
            .get::<TypeAttr>(&ATTR_KEY_CALLEE_TYPE)
            .unwrap()
            .get_type(ctx)
    }

    /// Set callee type
    fn set_callee_type(&self, ctx: &mut Context, callee_ty: Ptr<TypeObj>) {
        let mut self_op = self.get_operation().deref_mut(ctx);
        let ty_attr = TypeAttr::new(callee_ty);
        self_op
            .attributes
            .set(ATTR_KEY_CALLEE_TYPE.clone(), ty_attr);
    }
}
