use std::collections::hash_map;

use rustc_hash::FxHashMap;
use thiserror::Error;

use crate::{
    basic_block::BasicBlock,
    builtin::attributes::TypeAttr,
    context::{Context, Ptr},
    decl_op_interface,
    identifier::Identifier,
    linked_list::ContainsLinkedList,
    location::{Located, Location},
    op::{op_cast, Op},
    operation::Operation,
    printable::Printable,
    r#type::{TypeObj, TypePtr, Typed},
    region::Region,
    result::Result,
    use_def_lists::Value,
    verify_err, verify_error,
};

use super::{attributes::StringAttr, types::FunctionType};

decl_op_interface! {
    /// An [Op] implementing this interface is a block terminator.
    IsTerminatorInterface {
        fn verify(_op: &dyn Op, _ctx: &Context) -> Result<()>
        where
            Self: Sized,
        {
            Ok(())
        }
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

decl_op_interface! {
    /// This [terminator](IsTerminatorInterface) [Op] branches to
    /// other [BasicBlock]s, possibly passing arguments to the target block.
    ///
    /// This is similar to MLIR's
    /// [BranchOpInterface](https://github.com/llvm/llvm-project/blob/b1f04d57f5818914d7db506985e2932f217844bd/mlir/include/mlir/Interfaces/ControlFlowInterfaces.td)
    /// but is stricter: (1) Produced operands aren't supported, just forwarded.
    /// (2) Type of the value passed is expected to be the same as the target block argument.
    BranchOpInterface: IsTerminatorInterface {
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
                        op.get_operation().deref(ctx).loc(),
                        BranchOpInterfaceVerifyErr::SuccessorOperandsMismatch
                        { provided: operands.len(), expected: succ.get_num_arguments() }
                    );
                }
                for (idx, operand) in operands.iter().enumerate() {
                    let block_arg = succ.get_argument(idx);
                    if operand.get_type(ctx) != block_arg.get_type(ctx) {
                        return verify_err!(
                            op.get_operation().deref(ctx).loc(),
                            BranchOpInterfaceVerifyErr::SuccessorOperandTypeMismatch {
                                idx,
                                forwarded: operand.get_type(ctx).disp(ctx).to_string(),
                                expected: block_arg.get_type(ctx).disp(ctx).to_string(),
                            });
                    }
                }
            }
            Ok(())
        }
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

decl_op_interface! {
    /// Info on contained [Regions](crate::region::Region).
    RegionKindInterface {
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
}

#[derive(Error, Debug)]
#[error("Op {0} must have a single region")]
pub struct OneRegionVerifyErr(String);

decl_op_interface! {
    /// [Op]s that have exactly one region.
    OneRegionInterface {
        /// Get the single region that this [Op] has.
        fn get_region(&self, ctx: &Context) -> Ptr<Region> {
            self.get_operation()
                .deref(ctx)
                .get_region(0)
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
}

#[derive(Error, Debug)]
#[error("Op {0} must only have regions with single block")]
pub struct SingleBlockRegionVerifyErr(String);

decl_op_interface! {
    /// [Op]s with regions that have a single block.
    SingleBlockRegionInterface {
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
}

/// Key for symbol name attribute when the operation defines a symbol.
pub static ATTR_KEY_SYM_NAME: crate::Lazy<Identifier> =
    crate::Lazy::new(|| "builtin_sym_name".try_into().unwrap());

#[derive(Error, Debug)]
#[error("Op implementing SymbolOpInterface does not have a symbol defined")]
pub struct SymbolOpInterfaceErr;

decl_op_interface! {
    /// [Op] that defines or declares a [symbol](https://mlir.llvm.org/docs/SymbolsAndSymbolTables/#symbol).
    SymbolOpInterface {
        // Get the name of the symbol defined by this operation.
        fn get_symbol_name(&self, ctx: &Context) -> String {
            let self_op = self.get_operation().deref(ctx);
            let s_attr = self_op.attributes.get::<StringAttr>(&ATTR_KEY_SYM_NAME).unwrap();
            String::from(s_attr.clone())
        }

        /// Set a name for the symbol defined by this operation.
        fn set_symbol_name(&self, ctx: &mut Context, name: &str) {
            let name_attr = StringAttr::new(name.to_string());
            let mut self_op = self.get_operation().deref_mut(ctx);
            self_op.attributes.set(ATTR_KEY_SYM_NAME.clone(), name_attr);
        }

        fn verify(op: &dyn Op, ctx: &Context) -> Result<()>
        where
            Self: Sized,
        {
            let self_op = op.get_operation().deref(ctx);
            if self_op.attributes.get::<StringAttr>(&ATTR_KEY_SYM_NAME).is_none() {
                return verify_err!(op.get_operation().deref(ctx).loc(), SymbolOpInterfaceErr);
            }
            Ok(())
        }
    }
}

#[derive(Error, Debug)]
pub enum SymbolTableInterfaceErr {
    #[error("Multiple definitions of Symbol {0}")]
    SymbolRedefined(String),
}

decl_op_interface! {
    // Any [Op] that holds a symbol table.
    SymbolTableInterface: SingleBlockRegionInterface, OneRegionInterface {

        /// Lookup a symbol in this symbol table op. Linear search.
        fn lookup(&self, ctx: &Context, sym: String) -> Option<Ptr<Operation>> {
            for op in self.get_body(ctx, 0).deref(ctx).iter(ctx) {
                if let Some(sym_op) =
                    op_cast::<dyn SymbolOpInterface>(&*Operation::get_op(op, ctx))
                {
                    if sym_op.get_symbol_name(ctx) == sym {
                        return Some(op)
                    }
                }
            }
            None
        }

        fn verify(op: &dyn Op, ctx: &Context) -> Result<()>
        where
            Self: Sized,
        {
            // Check that every symbol is defined only once.
            let mut seen = FxHashMap::<String, Location>::default();
            let table_ops_block =
                op_cast::<dyn SingleBlockRegionInterface>(op)
                .unwrap()
                .get_body(ctx, 0);
            for op in table_ops_block.deref(ctx).iter(ctx) {
                if let Some(sym_op) =
                    op_cast::<dyn SymbolOpInterface>(&*Operation::get_op(op, ctx))
                {
                    let sym = sym_op.get_symbol_name(ctx);
                    match seen.entry(sym.clone()) {
                        hash_map::Entry::Occupied(prev_loc) => {
                            return verify_err!(
                                op.deref(ctx).loc(),
                                verify_error!(
                                    prev_loc.get().clone(),
                                    SymbolTableInterfaceErr::SymbolRedefined(sym)
                                ));
                        }
                        hash_map::Entry::Vacant(vac) => {
                            vac.insert(op.deref(ctx).loc());
                        }
                    }
                }
            }

            Ok(())
        }
    }
}

#[derive(Error, Debug)]
#[error("Op {0} must have single result")]
pub struct OneResultVerifyErr(pub String);

decl_op_interface! {
    /// An [Op] having exactly one result.
    OneResultInterface {
        /// Get the single result defined by this [Op].
        fn get_result(&self, ctx: &Context) -> Value {
            self.get_operation()
                .deref(ctx)
                .get_result(0)
        }

        /// Get the type of the single result defined by this [Op].
        fn result_type(&self, ctx: &Context) -> Ptr<TypeObj> {
            self.get_operation()
                .deref(ctx)
                .get_type(0)
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
}

#[derive(Error, Debug)]
#[error("Op {0} must not produce result(s)")]
pub struct ZeroResultVerifyErr(pub String);

decl_op_interface! {
    /// An [Op] having no results.
    ZeroResultInterface {
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
}

#[derive(Error, Debug)]
#[error("Op {0} must not have any operand")]
pub struct ZeroOpdVerifyErr(String);

decl_op_interface! {
    /// An [Op] having no operands.
    ZeroOpdInterface {
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
}

#[derive(Error, Debug)]
#[error("Op must have exactly one operand")]
pub struct OneOpdVerifyErr(String);

decl_op_interface! {
    /// An [Op] having no operands.
    OneOpdInterface {
        /// Get the single operand used by this [Op].
        fn get_operand(&self, ctx: &Context) -> Value {
            self.get_operation()
                .deref(ctx)
                .get_operand(0)
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
}

decl_op_interface! {
    /// An [Op] whose regions's SSA names are isolated from above.
    /// This is similar to (but not the same as) MLIR's
    /// [IsolatedFromAbove](https://mlir.llvm.org/docs/Traits/#isolatedfromabove) trait.
    /// Definition: all regions that are reachable / traversible in any
    /// direction in the region hierarchy without passing an `IsolatedFromAbove`
    /// barrier, share the same SSA name space.
    /// i.e., a region that is not `IsolatedFromAbove` cannot have any SSA name
    /// in common with that of any of its ancestors or siblings or cousins etc.
    IsolatedFromAboveInterface {
        fn verify(_op: &dyn Op, _ctx: &Context) -> Result<()>
        where
            Self: Sized,
        {
            Ok(())
        }
    }
}

#[derive(Error, Debug)]
pub enum SameOperandsTypeVerifyErr {
    #[error("Op with same operands types must have at least one operand")]
    NoOperands,
    #[error("Op has different operand types")]
    TypesDiffer,
}

decl_op_interface! {
    /// An [Op] with at least one operand, and them all having the same type.
    SameOperandsType {
        /// Get the common type of the operands.
        fn operand_type(&self, ctx: &Context) -> Ptr<TypeObj> {
            self.get_operation()
                .deref(ctx)
                .get_operand(0)
                .get_type(ctx)
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
}

#[derive(Error, Debug)]
pub enum SameResultsTypeVerifyErr {
    #[error("Op with same result types must have at least one result")]
    NoResults,
    #[error("Op has different result types")]
    TypesDiffer,
}

decl_op_interface! {
    // An [Op] with at least one result, and them all having the same type.
    SameResultsType {
        /// Get the common type of the results.
        fn result_type(&self, ctx: &Context) -> Ptr<TypeObj> {
            self.get_operation()
                .deref(ctx)
                .get_result(0)
                .get_type(ctx)
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
}

#[derive(Error, Debug)]
#[error("Op has different operand and result types")]
pub struct SameOperandsAndResultTypeVerifyErr;

decl_op_interface! {
    /// An [Op] with at least one result and one operand, and them all having the same type.
    /// See MLIR's [SameOperandsAndResultType](https://mlir.llvm.org/doxygen/classmlir_1_1OpTrait_1_1SameOperandsAndResultType.html).
    SameOperandsAndResultType: SameOperandsType, SameResultsType {
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
                return verify_err!(
                    op.get_operation().deref(ctx).loc(),
                    SameOperandsAndResultTypeVerifyErr
                );
            }

            Ok(())
        }
    }
}

/// A callable object is either a
///   - direct callee, expressed as a symbol)
///   - indirect callee, a [Value] pointing to the function to be called.
pub enum CallOpCallable {
    Direct(String),
    Indirect(Value),
}

#[derive(Error, Debug)]
pub enum CallOpInterfaceErr {
    #[error("Callee type attribute not found")]
    CalleeTypeAttrNotFoundErr,
    #[error("Callee type attribute must be FunctionType")]
    CalleeTypeAttrIncorrectTypeErr,
}

pub static ATTR_KEY_CALLEE_TYPE: crate::Lazy<Identifier> =
    crate::Lazy::new(|| "builtin_callee_type".try_into().unwrap());

decl_op_interface! {
    /// A call-like op: Transfers control from one function to another.
    /// See MLIR's [CallOpInterface](https://mlir.llvm.org/docs/Interfaces/#callinterfaces).
    CallOpInterface {
        fn verify(op: &dyn Op, ctx: &Context) -> Result<()>
        where
            Self: Sized,
        {
            let op = op.get_operation().deref(ctx);
            let Some(callee_type_attr) =
                op.attributes.get::<TypeAttr>(&ATTR_KEY_CALLEE_TYPE)
            else {
                return verify_err!(op.loc(), CallOpInterfaceErr::CalleeTypeAttrNotFoundErr);
            };
            if !callee_type_attr.get_type(ctx).deref(ctx).is::<FunctionType>() {
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
        fn callee_type(&self, ctx: &Context) -> TypePtr<FunctionType> {
            let self_op = self.get_operation().deref(ctx);
            let ty_attr = self_op.attributes.get::<TypeAttr>(&ATTR_KEY_CALLEE_TYPE).unwrap();
            TypePtr::from_ptr
                (ty_attr.get_type(ctx), ctx).expect("Incorrect callee type, not a FunctionType")
        }
    }
}
