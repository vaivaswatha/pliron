use std::marker::PhantomData;

use crate::{context::{ArenaObj, Ptr}, use_def_lists::{DefRef, UseRef}, value::Value, operation::Operation};

pub struct BlockArgument {}

impl Value for BlockArgument {
    fn get_defining_op(&self) -> Option<Ptr<Operation>> {
        None
    }

    fn get_parent_block(&self) -> Option<Ptr<BasicBlock>> {
        todo!()
    }

    fn get_def_index(&self) -> usize {
        todo!()
    }

    fn get_uses(&self) -> &Vec<UseRef> {
        todo!()
    }

    fn get_uses_mut(&mut self) -> &mut Vec<UseRef> {
        todo!()
    }

    fn build_defref(&self) -> DefRef {
        DefRef::BlockArgument {
            block: self.get_parent_block().unwrap(),
            arg_idx: self.get_def_index(),
        }
    }
}

pub struct BasicBlock {

}

impl ArenaObj for BasicBlock {
    fn get_arena(ctx: &crate::context::Context) -> &generational_arena::Arena<Self> {
        todo!()
    }
    fn get_arena_mut(ctx: &mut crate::context::Context) -> &mut generational_arena::Arena<Self> {
        todo!()
    }
    fn dealloc_sub_objects(ptr: crate::context::Ptr<Self>, ctx: &mut crate::context::Context) {
        todo!()
    }
    fn has_references(ptr: crate::context::Ptr<Self>, ctx: &crate::context::Context) -> bool {
        todo!()
    }
}
