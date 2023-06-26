use crate::{
    basic_block::BasicBlock,
    context::{Context, Ptr},
    error::CompilerError,
    linked_list::ContainsLinkedList,
    op::Op,
    operation::Operation,
    r#type::TypeObj,
    region::Region,
    use_def_lists::Value,
    with_context::AttachContext,
};

use super::attributes::StringAttr;

/// An [Op] implementing this interface is a block terminator.
pub trait IsTerminatorInterface: Op {
    fn verify(_op: &dyn Op, _ctx: &Context) -> Result<(), CompilerError>
    where
        Self: Sized,
    {
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
pub trait RegionKindInterface: Op {
    /// Return the kind of the region with the given index inside this operation.
    fn get_region_kind(idx: usize) -> RegionKind;
    /// Return true if the region with the given index inside this operation
    /// must require dominance to hold.
    fn has_ssa_dominance(idx: usize) -> bool;

    fn verify(_op: &dyn Op, _ctx: &Context) -> Result<(), CompilerError>
    where
        Self: Sized,
    {
        Ok(())
    }
}

/// [Op]s that have exactly one region.
pub trait OneRegionInterface: Op {
    fn get_region(&self, ctx: &Context) -> Ptr<Region> {
        self.get_operation()
            .deref(ctx)
            .get_region(0)
            .expect("Expected OneRegion Op to contain a region")
    }

    /// Checks that the operation has exactly one region.
    fn verify(op: &dyn Op, ctx: &Context) -> Result<(), CompilerError>
    where
        Self: Sized,
    {
        let self_op = op.get_operation().deref(ctx);
        if self_op.regions.len() != 1 {
            return Err(CompilerError::VerificationError {
                msg: format!(
                    "Op {} must have single region.",
                    op.get_opid().with_ctx(ctx)
                ),
            });
        }
        Ok(())
    }
}

/// [Op]s with regions that have a single block.
pub trait SingleBlockRegionInterface: Op {
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
    fn verify(op: &dyn Op, ctx: &Context) -> Result<(), CompilerError>
    where
        Self: Sized,
    {
        let self_op = op.get_operation().deref(ctx);
        for region in &self_op.regions {
            if region.deref(ctx).iter(ctx).count() != 1 {
                return Err(CompilerError::VerificationError {
                    msg: format!(
                        "SingleBlockRegion Op {} must have single region.",
                        self_op.get_opid().with_ctx(ctx)
                    ),
                });
            }
        }
        Ok(())
    }
}

/// [Op] that defines or declares a [symbol](https://mlir.llvm.org/docs/SymbolsAndSymbolTables/#symbol).
pub trait SymbolOpInterface: Op {
    // Get the name of the symbol defined by this operation.
    fn get_symbol_name(&self, ctx: &Context) -> String {
        let self_op = self.get_operation().deref(ctx);
        let s_attr = self_op.attributes.get(super::ATTR_KEY_SYM_NAME).unwrap();
        String::from(s_attr.downcast_ref::<StringAttr>().unwrap().clone())
    }

    /// Set a name for the symbol defined by this operation.
    fn set_symbol_name(&self, ctx: &mut Context, name: &str) {
        let name_attr = StringAttr::create(name.to_string());
        let mut self_op = self.get_operation().deref_mut(ctx);
        self_op
            .attributes
            .insert(super::ATTR_KEY_SYM_NAME, name_attr);
    }

    fn verify(_op: &dyn Op, _ctx: &Context) -> Result<(), CompilerError>
    where
        Self: Sized,
    {
        Ok(())
    }
}

/// An [Op] having exactly one result.
pub trait OneResultInterface: Op {
    /// Get the single result defined by this Op.
    fn get_result(&self, ctx: &Context) -> Value {
        self.get_operation()
            .deref(ctx)
            .get_result(0)
            .unwrap_or_else(|| {
                panic!(
                    "{} must have exactly one result",
                    self.get_opid().with_ctx(ctx)
                )
            })
    }

    // Get the type of the single result defined by this Op.
    fn get_type(&self, ctx: &Context) -> Ptr<TypeObj> {
        self.get_operation()
            .deref(ctx)
            .get_type(0)
            .unwrap_or_else(|| {
                panic!(
                    "{} must have exactly one result",
                    self.get_opid().with_ctx(ctx)
                )
            })
    }

    fn verify(op: &dyn Op, ctx: &Context) -> Result<(), CompilerError>
    where
        Self: Sized,
    {
        let op = &*op.get_operation().deref(ctx);
        if op.get_num_results() != 1 {
            return Err(CompilerError::VerificationError {
                msg: format!(
                    "Expected exactly one result on operation {}",
                    op.get_opid().with_ctx(ctx)
                ),
            });
        }
        Ok(())
    }
}

/// An [Op] that calls a function
pub trait CallOpInterface {
    /// Returns the symbol of the callee of this call operation.
    fn get_callee_sym(&self, ctx: &Context) -> String;

    fn verify(_op: &dyn Op, _ctx: &Context) -> Result<(), CompilerError>
    where
        Self: Sized,
    {
        Ok(())
    }
}

/// Returns the symbols of the callees of all the call operations in this operation.
pub trait GetCalleesInterface<T: CallOpInterface + Op>: Op {
    /// Returns the symbols of the callees of all the call operations in this operation.
    fn get_callees_syms(&self, ctx: &Context) -> Vec<String> {
        let self_op = self.get_operation().deref(ctx);
        let mut callees = Vec::new();
        for region in &self_op.regions {
            for block in region.deref(ctx).iter(ctx) {
                for op in block.deref(ctx).iter(ctx) {
                    if let Some(call_op) = op.deref(ctx).get_op(ctx).downcast_ref::<T>() {
                        callees.push(call_op.get_callee_sym(ctx));
                    }
                }
            }
        }
        callees
    }

    fn verify(_op: &dyn Op, _ctx: &Context) -> Result<(), CompilerError>
    where
        Self: Sized,
    {
        Ok(())
    }
}
