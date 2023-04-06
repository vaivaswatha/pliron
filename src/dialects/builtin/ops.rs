use crate::{
    attribute::{self, attr_cast, AttrObj},
    basic_block::BasicBlock,
    common_traits::{DisplayWithContext, Named, Verify},
    context::{Context, Ptr},
    declare_op,
    dialect::Dialect,
    error::CompilerError,
    linked_list::ContainsLinkedList,
    op::Op,
    operation::Operation,
    r#type::TypeObj,
    region::Region,
    with_context::AttachContext,
};

use super::{
    attr_interfaces::TypedAttrInterface,
    attributes::{FloatAttr, IntegerAttr, TypeAttr},
    op_interfaces::{OneRegionInterface, SingleBlockRegionInterface, SymbolOpInterface},
    types::FunctionType,
};

use intertrait::cast_to;

declare_op!(
    /// Represents a module, a top level container operation.
    ///
    /// See MLIR's [builtin.module](https://mlir.llvm.org/docs/Dialects/Builtin/#builtinmodule-mlirmoduleop).
    /// It contains a single [SSACFG](super::op_interfaces::RegionKind::SSACFG)
    /// region containing a single block which can contain any operations and
    /// does not have a terminator.
    ///
    /// Attributes:
    ///
    /// | key | value |
    /// |-----|-------|
    /// | [ATTR_KEY_SYM_NAME](super::ATTR_KEY_SYM_NAME) | [StringAttr](super::attributes::StringAttr) |
    ModuleOp,
    "module",
    "builtin"
);

impl AttachContext for ModuleOp {}
impl DisplayWithContext for ModuleOp {
    fn fmt(&self, ctx: &Context, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let region = self.get_region(ctx).with_ctx(ctx).to_string();
        write!(
            f,
            "{} @{} {{\n{}}}",
            self.get_opid().with_ctx(ctx),
            self.get_symbol_name(ctx),
            indent::indent_all_by(2, region),
        )
    }
}

impl Verify for ModuleOp {
    fn verify(&self, ctx: &Context) -> Result<(), CompilerError> {
        let op = &*self.op.deref(ctx);
        if op.regions.len() != 1 {
            return Err(CompilerError::VerificationError {
                msg: "ModuleOp must have single region.".to_string(),
            });
        }
        op.regions[0].deref(ctx).verify(ctx)
    }
}

impl ModuleOp {
    /// Create a new [ModuleOp].
    /// The underlying [Operation] is not linked to a [BasicBlock](crate::basic_block::BasicBlock).
    /// The returned module has a single [Region] with a single (BasicBlock)[crate::basic_block::BasicBlock].
    pub fn new(ctx: &mut Context, name: &str) -> ModuleOp {
        let op = Operation::new(ctx, Self::get_opid_static(), vec![], vec![]);
        let opop = ModuleOp { op };
        opop.set_symbol_name(ctx, name);

        // Create a single region with an empty block.
        let region = Region::new(ctx, op);
        let block = BasicBlock::new(ctx, None, vec![]);
        block.insert_at_front(region, ctx);
        let opref = &mut *op.deref_mut(ctx);
        opref.regions.push(region);

        opop
    }

    /// Add an [Operation] into this module.
    pub fn add_operation(&self, ctx: &mut Context, op: Ptr<Operation>) {
        self.append_operation(ctx, op, 0)
    }
}

impl OneRegionInterface for ModuleOp {}
impl SingleBlockRegionInterface for ModuleOp {}
#[cast_to]
impl SymbolOpInterface for ModuleOp {}

declare_op!(
    /// An operation with a name containing a single SSA control-flow-graph region.
    /// See MLIR's [func.func](https://mlir.llvm.org/docs/Dialects/Func/#funcfunc-mlirfuncfuncop).
    ///
    /// Attributes:
    ///
    /// | key | value |
    /// |-----|-------|
    /// | [ATTR_KEY_SYM_NAME](super::ATTR_KEY_SYM_NAME) | [StringAttr](super::attributes::StringAttr) |
    /// | [ATTR_KEY_FUNC_TYPE](FuncOp::ATTR_KEY_FUNC_TYPE) | [TypeAttr](super::attributes::TypeAttr) |
    FuncOp,
    "func",
    "builtin"
);

impl FuncOp {
    /// Attribute key for the constant value.
    pub const ATTR_KEY_FUNC_TYPE: &str = "func.type";

    /// Create a new [FuncOp].
    /// The underlying [Operation] is not linked to a [BasicBlock](crate::basic_block::BasicBlock).
    /// The returned function has a single region with an empty `entry` block.
    pub fn new_unlinked(ctx: &mut Context, name: &str, ty: Ptr<TypeObj>) -> FuncOp {
        let ty_attr = TypeAttr::create(ty);
        let op = Operation::new(ctx, Self::get_opid_static(), vec![], vec![]);

        // Create a body region with an empty entry block.
        let region = Region::new(ctx, op);
        let body = BasicBlock::new(ctx, Some("entry".to_string()), vec![]);
        body.insert_at_front(region, ctx);
        {
            let opref = &mut *op.deref_mut(ctx);
            opref.regions.push(region);
            // Set function type attributes.
            opref.attributes.insert(Self::ATTR_KEY_FUNC_TYPE, ty_attr);
        }
        let opop = FuncOp { op };
        opop.set_symbol_name(ctx, name);

        opop
    }

    pub fn get_type(&self, ctx: &Context) -> Ptr<TypeObj> {
        let opref = self.get_operation().deref(ctx);
        let ty_attr = opref.attributes.get(Self::ATTR_KEY_FUNC_TYPE).unwrap();
        attr_cast::<dyn TypedAttrInterface>(&**ty_attr)
            .unwrap()
            .get_type()
    }

    pub fn get_entry_block(&self, ctx: &Context) -> Ptr<BasicBlock> {
        self.get_region(ctx).deref(ctx).get_head().unwrap()
    }
}

impl OneRegionInterface for FuncOp {}
#[cast_to]
impl SymbolOpInterface for FuncOp {}

impl AttachContext for FuncOp {}
impl DisplayWithContext for FuncOp {
    fn fmt(&self, ctx: &Context, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let region = self.get_region(ctx).with_ctx(ctx).to_string();
        write!(
            f,
            "{} @{}{} {{\n{}}}",
            self.get_opid().with_ctx(ctx),
            self.get_symbol_name(ctx),
            self.get_type(ctx).with_ctx(ctx),
            indent::indent_all_by(2, region),
        )
    }
}

impl Verify for FuncOp {
    fn verify(&self, ctx: &Context) -> Result<(), CompilerError> {
        let ty = self.get_type(ctx);
        if !(ty.deref(ctx).is::<FunctionType>()) {
            return Err(CompilerError::VerificationError {
                msg: "Unexpected Func type".to_string(),
            });
        }
        let op = &*self.get_operation().deref(ctx);
        if op.get_opid() != Self::get_opid_static() {
            return Err(CompilerError::VerificationError {
                msg: "Incorrect OpId".to_string(),
            });
        }
        if op.get_num_results() != 0 || op.get_num_operands() != 0 {
            return Err(CompilerError::VerificationError {
                msg: "Incorrect number of results or operands".to_string(),
            });
        }
        Ok(())
    }
}

declare_op!(
    /// Numeric constant.
    /// See MLIR's [arith.constant](https://mlir.llvm.org/docs/Dialects/ArithOps/#arithconstant-mlirarithconstantop).
    ///
    /// Attributes:
    ///
    /// | key | value |
    /// |-----|-------|
    /// |[ATTR_KEY_VALUE](ConstantOp::ATTR_KEY_VALUE) | [IntegerAttr] or [FloatAttr] |
    ///
    /// Results:
    ///
    /// | result | description |
    /// |-----|-------|
    /// | `result` | any type |
    ConstantOp,
    "constant",
    "builtin"
);

impl ConstantOp {
    /// Attribute key for the constant value.
    pub const ATTR_KEY_VALUE: &str = "constant.value";
    /// Get the constant value that this Op defines.
    pub fn get_value(&self, ctx: &Context) -> AttrObj {
        let op = self.get_operation().deref(ctx);
        let value = op.attributes.get(Self::ATTR_KEY_VALUE).unwrap();
        if value.is::<IntegerAttr>() {
            attribute::clone::<IntegerAttr>(value)
        } else {
            attribute::clone::<FloatAttr>(value)
        }
    }

    /// Create a new [ConstantOp]. The underlying [Operation] is not linked to a
    /// [BasicBlock](crate::basic_block::BasicBlock).
    pub fn new_unlinked(ctx: &mut Context, value: AttrObj) -> ConstantOp {
        let result_type = attr_cast::<dyn TypedAttrInterface>(&*value)
            .expect("ConstantOp const value must provide TypedAttrInterface")
            .get_type();
        let op = Operation::new(ctx, Self::get_opid_static(), vec![result_type], vec![]);
        op.deref_mut(ctx)
            .attributes
            .insert(Self::ATTR_KEY_VALUE, value);
        ConstantOp { op }
    }
}

impl AttachContext for ConstantOp {}
impl DisplayWithContext for ConstantOp {
    fn fmt(&self, ctx: &Context, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "{} = {} {}",
            self.get_opid().with_ctx(ctx),
            self.get_operation()
                .deref(ctx)
                .get_result(0)
                .unwrap()
                .get_name(ctx),
            self.get_value(ctx).with_ctx(ctx)
        )
    }
}

impl Verify for ConstantOp {
    fn verify(&self, ctx: &Context) -> Result<(), CompilerError> {
        let value = self.get_value(ctx);
        if !(value.is::<IntegerAttr>() || value.is::<FloatAttr>()) {
            return Err(CompilerError::VerificationError {
                msg: "Unexpected constant type".to_string(),
            });
        }
        let op = &*self.get_operation().deref(ctx);
        if op.get_opid() != Self::get_opid_static() {
            return Err(CompilerError::VerificationError {
                msg: "Incorrect OpId".to_string(),
            });
        }
        if op.get_num_results() != 1 || op.get_num_operands() != 0 {
            return Err(CompilerError::VerificationError {
                msg: "Incorrect number of results or operands".to_string(),
            });
        }
        Ok(())
    }
}

pub fn register(ctx: &mut Context, dialect: &mut Dialect) {
    ModuleOp::register(ctx, dialect);
    FuncOp::register(ctx, dialect);
    ConstantOp::register(ctx, dialect);
}
