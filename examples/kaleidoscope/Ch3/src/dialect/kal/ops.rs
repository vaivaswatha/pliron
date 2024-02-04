use pliron::attribute::{attr_cast, AttrObj, Attribute};
use pliron::basic_block::BasicBlock;
use pliron::context::Ptr;
use pliron::dialect::Dialect;
use pliron::dialects::builtin::attr_interfaces::TypedAttrInterface;
use pliron::dialects::builtin::attributes::{StringAttr, TypeAttr};
use pliron::dialects::builtin::op_interfaces::{
    CallOpInterface, OneRegionInterface, OneResultInterface, SingleBlockRegionInterface,
    SymbolOpInterface, ZeroOpdInterface, ZeroResultInterface,
};
use pliron::dialects::builtin::types::FunctionType;
use pliron::error::Result;
use pliron::impl_op_interface;
use pliron::linked_list::ContainsLinkedList;
use pliron::op::Op;
use pliron::operation::Operation;
use pliron::parsable::Parsable;
use pliron::printable::Printable;
use pliron::r#type::TypeObj;
use pliron::use_def_lists::Value;
use pliron::{common_traits::Verify, context::Context};
use pliron_derive::{def_op, NotParsableOp, Printable};

use super::{BinOpAttr, BinaryOperator, BoolType, NumberType, ParamsAttr, ATTR_KEY_CALLEE_NAME};

pub(super) fn register(ctx: &mut Context, dialect: &mut Dialect) {
    BinOp::register(ctx, dialect, BinOp::parser_fn);
    CallOp::register(ctx, dialect, CallOp::parser_fn);
    VarOp::register(ctx, dialect, VarOp::parser_fn);
    ConstOp::register(ctx, dialect, ConstOp::parser_fn);
    ExternOp::register(ctx, dialect, ExternOp::parser_fn);
    EvalOp::register(ctx, dialect, EvalOp::parser_fn);
    ReturnOp::register(ctx, dialect, ReturnOp::parser_fn);
    FuncOp::register(ctx, dialect, FuncOp::parser_fn);
}

#[def_op]
#[op_name = "kal.bin_op"]
#[derive(PartialEq, Hash, Printable, NotParsableOp)]
pub struct BinOp {}
impl Verify for BinOp {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}
impl_op_interface!( OneResultInterface for BinOp {});
impl BinOp {
    pub fn new_unlinked(ctx: &mut Context, binop: BinaryOperator, lhs: Value, rhs: Value) -> Self {
        let result_type = match binop {
            BinaryOperator::LessThan => vec![BoolType::get(ctx)],
            _ => vec![NumberType::get(ctx)],
        };
        let operands = vec![lhs, rhs];
        let op = Operation::new(ctx, Self::get_opid_static(), result_type, operands, 0);
        let op = Self { op };
        ins_attr(&op, ctx, BinOpAttr::KEY, BinOpAttr::create(binop));
        op
    }

    pub fn get_binop(&self, ctx: &Context) -> BinaryOperator {
        with_attr(self, ctx, BinOpAttr::KEY, |attr: &BinOpAttr| attr.op())
    }

    pub fn get_lhs(&self, ctx: &Context) -> Value {
        self.get_operation()
            .deref(ctx)
            .get_operand(0)
            .unwrap_or_else(|| panic!("{} must have lhs", self.get_opid().disp(ctx)))
    }

    pub fn get_rhs(&self, ctx: &Context) -> Value {
        self.get_operation()
            .deref(ctx)
            .get_operand(1)
            .unwrap_or_else(|| panic!("{} must have rhs", self.get_opid().disp(ctx)))
    }
}

#[def_op]
#[op_name = "kal.call"]
#[derive(PartialEq, Hash, Printable, NotParsableOp)]
pub struct CallOp {}
impl Verify for CallOp {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}
impl_op_interface!( CallOpInterface for CallOp {
    fn get_callee_sym(&self, ctx: &Context) -> String {
        with_attr(self, ctx, ATTR_KEY_CALLEE_NAME, |attr: &StringAttr| {
            String::from(attr.clone())
        })
    }
});
impl_op_interface!( OneResultInterface for CallOp {});
impl CallOp {
    pub fn new_unlinked(ctx: &mut Context, callee: String, args: Vec<Value>) -> Self {
        let result_type = vec![NumberType::get(ctx)];
        let op = Operation::new(ctx, Self::get_opid_static(), result_type, args, 0);
        let cop = Self { op };
        cop.set_callee_sym(ctx, callee);
        cop
    }

    fn set_callee_sym(&self, ctx: &mut Context, callee: String) {
        ins_attr(self, ctx, ATTR_KEY_CALLEE_NAME, StringAttr::create(callee));
    }
}

#[def_op]
#[op_name = "kal.var"]
#[derive(PartialEq, Hash, Printable, NotParsableOp)]
pub struct VarOp {}
impl Verify for VarOp {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}
impl_op_interface!( SymbolOpInterface for VarOp {});
impl_op_interface!( ZeroOpdInterface for VarOp {});
impl_op_interface!( OneResultInterface for VarOp {});
impl VarOp {
    pub fn new_unlinked(ctx: &mut Context, name: &str) -> Self {
        let result_type = vec![NumberType::get(ctx)];
        let op = Operation::new(ctx, Self::get_opid_static(), result_type, vec![], 0);
        let vop = Self { op };
        vop.set_symbol_name(ctx, name);
        vop
    }
}

#[def_op]
#[op_name = "kal.const"]
#[derive(PartialEq, Hash, Printable, NotParsableOp)]
pub struct ConstOp {}
impl Verify for ConstOp {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}
impl_op_interface! (ZeroOpdInterface for ConstOp {});
impl_op_interface! (OneResultInterface for ConstOp {});
impl ConstOp {
    /// Attribute key for the constant value.
    pub const ATTR_KEY_VALUE: &'static str = "constant.value";

    pub fn new_unlinked(ctx: &mut Context, value: AttrObj) -> Self {
        let result_type = attr_cast::<dyn TypedAttrInterface>(&*value)
            .expect("ConstantOp const value must provide TypedAttrInterface")
            .get_type();
        let op = Operation::new(ctx, Self::get_opid_static(), vec![result_type], vec![], 0);
        op.deref_mut(ctx)
            .attributes
            .insert(Self::ATTR_KEY_VALUE, value);
        ConstOp { op }
    }

    /// Get the constant value that this Op defines.
    pub fn get_value(&self, ctx: &Context) -> AttrObj {
        let op = self.get_operation().deref(ctx);
        op.attributes.get(Self::ATTR_KEY_VALUE).unwrap().clone()
    }
}

#[def_op]
#[op_name = "kal.func"]
#[derive(PartialEq, Hash, Printable, NotParsableOp)]
pub struct FuncOp {}
impl Verify for FuncOp {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}
impl_op_interface!(SymbolOpInterface for FuncOp {});
impl_op_interface!(SingleBlockRegionInterface for FuncOp {});
impl_op_interface!(OneRegionInterface for FuncOp {});
impl FuncOp {
    /// Attribute key for the constant value.
    pub const ATTR_KEY_FUNC_TYPE: &'static str = "func.type";

    pub fn new_unlinked(ctx: &mut Context, name: &str, ty: Ptr<TypeObj>) -> FuncOp {
        let ty_attr = TypeAttr::create(ty);
        let op = Operation::new(ctx, Self::get_opid_static(), vec![], vec![], 1);

        let arg_types = {
            let fn_tyref = ty.deref(ctx);
            let fn_ty = fn_tyref.downcast_ref::<FunctionType>().unwrap();
            fn_ty.get_inputs().clone()
        };

        // Create an empty entry block.
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

        opop
    }

    /// Get the function signature (type).
    pub fn get_type(&self, ctx: &Context) -> Ptr<TypeObj> {
        let opref = self.get_operation().deref(ctx);
        let ty_attr = opref.attributes.get(Self::ATTR_KEY_FUNC_TYPE).unwrap();
        attr_cast::<dyn TypedAttrInterface>(&**ty_attr)
            .unwrap()
            .get_type()
    }

    /// Get the entry block of this function.
    pub fn get_entry_block(&self, ctx: &Context) -> Ptr<BasicBlock> {
        self.get_region(ctx).deref(ctx).get_head().unwrap()
    }

    /// Get an iterator over all operations.
    pub fn op_iter<'a>(&self, ctx: &'a Context) -> impl Iterator<Item = Ptr<Operation>> + 'a {
        self.get_region(ctx)
            .deref(ctx)
            .iter(ctx)
            .flat_map(|bb| bb.deref(ctx).iter(ctx))
    }
}

#[def_op]
#[op_name = "kal.return"]
#[derive(PartialEq, Hash, Printable, NotParsableOp)]
pub struct ReturnOp {}
impl Verify for ReturnOp {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}
impl_op_interface!( ZeroResultInterface for ReturnOp {});
impl ReturnOp {
    pub fn new_unlinked(ctx: &mut Context, value: Value) -> Self {
        let op = Operation::new(ctx, Self::get_opid_static(), vec![], vec![value], 0);
        Self { op }
    }
}

#[def_op]
#[op_name = "kal.extern"]
#[derive(PartialEq, Hash, Printable, NotParsableOp)]
pub struct ExternOp {}
impl Verify for ExternOp {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}
impl_op_interface!( SymbolOpInterface for ExternOp {});
impl_op_interface!( ZeroResultInterface for ExternOp {});
impl_op_interface!( ZeroOpdInterface for ExternOp {});
impl ExternOp {
    pub fn new_unlinked(ctx: &mut Context, name: &str, params: Vec<String>) -> Self {
        let op = Operation::new(ctx, Self::get_opid_static(), vec![], vec![], 0);
        let eop = Self { op };
        eop.set_symbol_name(ctx, name);
        ins_attr(&eop, ctx, ParamsAttr::KEY, ParamsAttr::create(params));
        eop
    }

    pub fn get_parameters(&self, ctx: &Context) -> Vec<String> {
        with_attr(self, ctx, ParamsAttr::KEY, |attr: &ParamsAttr| {
            attr.params()
        })
    }
}

#[def_op]
#[op_name = "kal.eval"]
#[derive(PartialEq, Hash, Printable, NotParsableOp)]
pub struct EvalOp {}
impl Verify for EvalOp {
    fn verify(&self, _ctx: &Context) -> Result<()> {
        Ok(())
    }
}
impl_op_interface!( ZeroResultInterface for EvalOp {});
impl EvalOp {
    pub fn new_unlinked(ctx: &mut Context, value: Value) -> Self {
        let op = Operation::new(ctx, Self::get_opid_static(), vec![], vec![value], 0);
        Self { op }
    }
}

fn with_attr<O: Op, A: Attribute, T, F>(op: &O, ctx: &Context, key: &str, f: F) -> T
where
    F: FnOnce(&A) -> T,
{
    let self_op = op.get_operation().deref(ctx);
    let attr = self_op.attributes.get(key).unwrap();
    f(attr.downcast_ref::<A>().unwrap())
}

fn ins_attr<O: Op>(op: &O, ctx: &mut Context, key: &'static str, attr: AttrObj) -> Option<AttrObj> {
    let mut self_op = op.get_operation().deref_mut(ctx);
    self_op.attributes.insert(key, attr)
}
