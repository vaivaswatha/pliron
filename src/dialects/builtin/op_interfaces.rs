use crate::{
    basic_block::BasicBlock,
    context::{Context, Ptr},
    linked_list::ContainsLinkedList,
    op::Op,
    operation::Operation,
    region::Region,
    use_def_lists::Value,
};

use super::attributes::StringAttr;

/// An [Op] implementing this interface is a block terminator.
pub trait IsTerminatorInterface: Op {}

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
}

/// [Op]s that have exactly one region.
pub trait OneRegionInterface: Op {
    fn get_region(&self, ctx: &Context) -> Ptr<Region> {
        *self
            .get_operation()
            .deref(ctx)
            .regions
            .get(0)
            .expect("Expected OneRegion Op to contain a region")
    }
}

/// [Op]s with regions that have a single block.
pub trait SingleBlockRegionInterface: Op {
    fn get_body(&self, ctx: &Context, region_idx: usize) -> Ptr<BasicBlock> {
        self.get_operation().deref(ctx).regions[region_idx]
            .deref(ctx)
            .get_head()
            .expect("Expected SingleBlockRegion Op to contain a block")
    }

    fn append_operation(&self, ctx: &mut Context, op: Ptr<Operation>, region_idx: usize) {
        op.insert_at_back(self.get_body(ctx, region_idx), ctx);
    }
}

/// [Op] that defines or declares a [symbol](https://mlir.llvm.org/docs/SymbolsAndSymbolTables/#symbol).
pub trait SymbolOpInterface: Op {
    fn get_symbol_name(&self, ctx: &Context) -> String {
        let self_op = self.get_operation().deref(ctx);
        let s_attr = self_op.attributes.get(super::ATTR_KEY_SYM_NAME).unwrap();
        String::from(s_attr.downcast_ref::<StringAttr>().unwrap().clone())
    }

    fn set_symbol_name(&self, ctx: &mut Context, name: &str) {
        let name_attr = StringAttr::create(name.to_string());
        let mut self_op = self.get_operation().deref_mut(ctx);
        self_op
            .attributes
            .insert(super::ATTR_KEY_SYM_NAME, name_attr);
    }
}

/// An [Op] having exactly one result.
pub trait OneResultInterface: Op {
    fn get_result(&self, ctx: &Context) -> Value;
}
