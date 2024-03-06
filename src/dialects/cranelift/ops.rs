use cranelift_module::Linkage;
use pliron_derive::{def_op, NotParsable, Printable};

use crate::basic_block::BasicBlock;
use crate::context::Ptr;
use crate::dialects::builtin::attributes::TypeAttr;
use crate::dialects::builtin::op_interfaces::{
    IsolatedFromAboveInterface, OneRegionInterface, SymbolOpInterface,
};
use crate::dialects::builtin::types::FunctionType;
use crate::error::Result;
use crate::impl_op_interface;
use crate::op::Op;
use crate::operation::Operation;
use crate::parsable::Parsable;
use crate::r#type::TypeObj;
use crate::{common_traits::Verify, context::Context, dialect::Dialect};

use super::attributes::LinkageAttr;

pub fn register(ctx: &mut Context, dialect: &mut Dialect) {
    FuncOp::register(ctx, dialect, FuncOp::parser_fn);
}

#[def_op("cranelift.func")]
#[derive(Printable, NotParsable)]
pub struct FuncOp {}
impl Verify for FuncOp {
    fn verify(&self, ctx: &Context) -> Result<()> {
        Ok(())
    }
}

impl_op_interface!(OneRegionInterface for FuncOp {});
impl_op_interface!(SymbolOpInterface for FuncOp {});
impl_op_interface!(IsolatedFromAboveInterface for FuncOp {});

impl FuncOp {
    /// Attribute key for the constant value.
    pub const ATTR_KEY_FUNC_TYPE: &'static str = "func.type";
    pub const ATTR_KEY_LINKAGE: &'static str = "func.linkage";

    /// Create a new [FuncOp].
    /// The underlying [Operation] is not linked to a [BasicBlock].
    /// The returned function has a single region with an empty `entry` block.
    pub fn new_unlinked(
        ctx: &mut Context,
        name: &str,
        linkage: Linkage,
        ty: Ptr<TypeObj>,
    ) -> FuncOp {
        let ty_attr = TypeAttr::create(ty);
        let op = Operation::new(ctx, Self::get_opid_static(), vec![], vec![], 1);

        // Create an empty entry block.
        let arg_types = {
            let fn_tyref = ty.deref(ctx);
            let fn_ty = fn_tyref.downcast_ref::<FunctionType>().unwrap();
            fn_ty.get_inputs().clone()
        };
        let region = op.deref_mut(ctx).get_region(0).unwrap();
        let body = BasicBlock::new(ctx, Some("entry".into()), arg_types);
        body.insert_at_front(region, ctx);
        {
            let opref = &mut *op.deref_mut(ctx);
            // Set function type attributes.
            opref.attributes.insert(Self::ATTR_KEY_FUNC_TYPE, ty_attr);
        }

        let opop = FuncOp { op };
        opop.set_symbol_name(ctx, name);
        opop.set_linkage(ctx, linkage);

        opop
    }

    pub fn get_linkage(&self, ctx: &Context) -> Linkage {
        let opref = self.op.deref(ctx);
        let linkage_attr = opref.attributes.get(Self::ATTR_KEY_LINKAGE).unwrap();
        let linkage_attr = linkage_attr.downcast_ref::<LinkageAttr>().unwrap();
        linkage_attr.linkage
    }

    pub fn set_linkage(&self, ctx: &Context, linkage: Linkage) {
        let mut opref = self.op.deref_mut(ctx);
        let linkage_attr = LinkageAttr::create(linkage);
        opref
            .attributes
            .insert(Self::ATTR_KEY_LINKAGE, linkage_attr);
    }
}
