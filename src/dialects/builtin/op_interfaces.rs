use thiserror::Error;

use crate::{
    basic_block::BasicBlock,
    context::{Context, Ptr},
    error::Result,
    linked_list::ContainsLinkedList,
    op::{op_cast, Op},
    operation::Operation,
    printable::Printable,
    r#type::TypeObj,
    region::Region,
    use_def_lists::Value,
    verify_err,
};

use super::attributes::StringAttr;

/// An [Op] implementing this interface is a block terminator.
pub trait IsTerminatorInterface: Op {
    fn verify(_op: &dyn Op, _ctx: &Context) -> Result<()>
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
pub trait OneRegionInterface: Op {
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
            return verify_err!(OneRegionVerifyErr(op.get_opid().to_string()));
        }
        Ok(())
    }
}

#[derive(Error, Debug)]
#[error("Op {0} must only have regions with single block")]
pub struct SingleBlockRegionVerifyErr(String);

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
    fn verify(op: &dyn Op, ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        let self_op = op.get_operation().deref(ctx);
        for region in &self_op.regions {
            if region.deref(ctx).iter(ctx).count() != 1 {
                return verify_err!(SingleBlockRegionVerifyErr(self_op.get_opid().to_string()));
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
pub trait OneResultInterface: Op {
    /// Get the single result defined by this Op.
    fn get_result(&self, ctx: &Context) -> Value {
        self.get_operation()
            .deref(ctx)
            .get_result(0)
            .unwrap_or_else(|| panic!("{} must have exactly one result", self.get_opid().disp(ctx)))
    }

    // Get the type of the single result defined by this Op.
    fn get_type(&self, ctx: &Context) -> Ptr<TypeObj> {
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
            return verify_err!(OneResultVerifyErr(op.get_opid().to_string()));
        }
        Ok(())
    }
}

#[derive(Error, Debug)]
#[error("Op {0} must not produce result(s)")]
pub struct ZeroResultVerifyErr(pub String);

/// An [Op] having no results.
pub trait ZeroResultInterface: Op {
    fn verify(op: &dyn Op, ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        let op = &*op.get_operation().deref(ctx);
        if op.get_num_results() != 0 {
            return verify_err!(ZeroResultVerifyErr(op.get_opid().to_string()));
        }
        Ok(())
    }
}

/// An [Op] that calls a function
pub trait CallOpInterface: Op {
    /// Returns the symbol of the callee of this call operation.
    fn get_callee_sym(&self, ctx: &Context) -> String;

    fn verify(_op: &dyn Op, _ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        Ok(())
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

/// An [Op] having no operands.
pub trait ZeroOpdInterface: Op {
    fn verify(op: &dyn Op, ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        let op = &*op.get_operation().deref(ctx);
        if op.get_num_operands() != 0 {
            return verify_err!(ZeroOpdVerifyErr(op.get_opid().to_string()));
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
pub trait IsolatedFromAboveInterface: Op {
    fn verify(_op: &dyn Op, _ctx: &Context) -> Result<()>
    where
        Self: Sized,
    {
        Ok(())
    }
}
