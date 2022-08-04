use std::marker::PhantomData;

use generational_arena;

use crate::{
    basic_block::BasicBlock,
    context::{ArenaObj, Context, Ptr},
    use_def_lists::{Def, DefRef, UseRef},
    value::{Operand, Value},
};

pub struct OpResult {
    def: Def,
}

impl Value for OpResult {
    fn get_defining_op(&self) -> Option<Ptr<Operation>> {
        todo!()
    }

    fn get_parent_block(&self) -> Option<Ptr<BasicBlock>> {
        todo!()
    }

    fn get_def_index(&self) -> usize {
        todo!()
    }

    fn get_uses(&self) -> &Vec<UseRef> {
        &self.def.uses
    }

    fn get_uses_mut(&mut self) -> &mut Vec<UseRef> {
        &mut self.def.uses
    }

    fn build_defref(&self) -> DefRef {
        DefRef::OpResult {
            op: self.get_defining_op().unwrap(),
            res_idx: self.get_def_index(),
        }
    }
}

#[derive(Debug)]
pub struct Operation {
    pub self_ptr: Ptr<Operation>,
}

impl Operation {
    pub fn get_operand_mut(&mut self, opd_idx: usize) -> Option<&mut Operand> {
        todo!()
    }
    pub fn new(ctx: &mut Context) -> Ptr<Operation> {
        Self::alloc(ctx, |self_ptr: Ptr<Operation>| Operation { self_ptr })
    }
}

impl ArenaObj for Operation {
    fn get_arena(ctx: &Context) -> &generational_arena::Arena<Self> {
        &ctx.operations
    }
    fn get_arena_mut(ctx: &mut Context) -> &mut generational_arena::Arena<Self> {
        todo!()
    }
    fn dealloc_sub_objects(ptr: Ptr<Self>, ctx: &mut Context) {
        todo!()
    }
    fn has_references(ptr: Ptr<Self>, ctx: &Context) -> bool {
        todo!()
    }
}
