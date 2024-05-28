use thiserror::Error;

use crate::{
    basic_block::BasicBlock,
    context::{Context, Ptr},
    decl_op_interface,
    error::Result,
    linked_list::ContainsLinkedList,
    location::Located,
    op::{op_cast, Op},
    operation::Operation,
    printable::Printable,
    r#type::{TypeObj, Typed},
    region::Region,
    use_def_lists::Value,
    verify_err,
};

use super::attributes::StringAttr;

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
                    let block_arg = succ.get_argument(idx).unwrap();
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
                .expect("Expected OneRegion Op to contain a region")
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
                .expect("Expected SingleBlockRegion Op to contain a region")
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

decl_op_interface! {
    /// [Op] that defines or declares a [symbol](https://mlir.llvm.org/docs/SymbolsAndSymbolTables/#symbol).
    SymbolOpInterface {
        // Get the name of the symbol defined by this operation.
        fn get_symbol_name(&self, ctx: &Context) -> String {
            let self_op = self.get_operation().deref(ctx);
            let s_attr = self_op.attributes.get::<StringAttr>(super::ATTR_KEY_SYM_NAME).unwrap();
            String::from(s_attr.clone())
        }

        /// Set a name for the symbol defined by this operation.
        fn set_symbol_name(&self, ctx: &mut Context, name: &str) {
            let name_attr = StringAttr::new(name.to_string());
            let mut self_op = self.get_operation().deref_mut(ctx);
            self_op.attributes.set(super::ATTR_KEY_SYM_NAME, name_attr);
        }

        fn verify(_op: &dyn Op, _ctx: &Context) -> Result<()>
        where
            Self: Sized,
        {
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
                .unwrap_or_else(|| panic!("{} must have exactly one result", self.get_opid().disp(ctx)))
        }

        /// Get the type of the single result defined by this [Op].
        fn result_type(&self, ctx: &Context) -> Ptr<TypeObj> {
            self.get_operation()
                .deref(ctx)
                .get_type(0)
                .unwrap_or_else(|| panic!("{} must have exactly one result", self.get_opid().disp(ctx)))
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

decl_op_interface! {
    /// An [Op] that calls a function
    CallOpInterface {
        /// Returns the symbol of the callee of this call [Op].
        fn get_callee_sym(&self, ctx: &Context) -> String;

        fn verify(_op: &dyn Op, _ctx: &Context) -> Result<()>
        where
            Self: Sized,
        {
            Ok(())
        }
    }
}

/// Returns the symbols of the callees of all the call operations in this operation.
pub fn get_callees_syms(ctx: &Context, op: Ptr<Operation>) -> Vec<String> {
    let ref_op = op.deref(ctx);
    let mut callees = Vec::new();
    for region in &ref_op.regions {
        for block in region.deref(ctx).iter(ctx) {
            for op in block.deref(ctx).iter(ctx) {
                if let Some(call_op) =
                    op_cast::<dyn CallOpInterface>(Operation::get_op(op, ctx).as_ref())
                {
                    callees.push(call_op.get_callee_sym(ctx));
                }
            }
        }
    }
    callees
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
                .unwrap_or_else(|| {
                    panic!(
                        "{} must have exactly one operand",
                        self.get_opid().disp(ctx)
                    )
                })
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
                return verify_err!(op.loc(), ZeroOpdVerifyErr(op.get_opid().to_string()));
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
                .expect("Expected at least one operand")
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
                .expect("Expected at least one result")
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
