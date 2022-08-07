use std::marker::PhantomData;

use crate::{
    context::{ArenaObj, Context, Ptr},
    operation::Operation,
    use_def_lists::{Def, DefRef, Use, UseRef},
    value::Value,
    vec_exns::VecExtns,
};

#[derive(Debug)]
pub struct BlockArgument {
    def: Def,
}

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

    fn add_use(&mut self, r#use: UseRef) -> Use {
        let use_idx = self.def.uses.push_back(r#use);
        Use {
            def: DefRef::BlockArgument {
                block: self.get_parent_block().unwrap(),
                arg_idx: self.get_def_index(),
            },
            use_idx,
        }
    }
}

#[derive(Debug)]
pub struct BasicBlock {}

impl ArenaObj for BasicBlock {
    fn get_arena(ctx: &Context) -> &generational_arena::Arena<Self> {
        todo!()
    }
    fn get_arena_mut(ctx: &mut Context) -> &mut generational_arena::Arena<Self> {
        todo!()
    }
    fn dealloc_sub_objects(ptr: Ptr<Self>, ctx: &mut Context) {
        todo!()
    }
    fn remove_references(ptr: Ptr<Self>, ctx: &mut Context) {
        todo!()
    }
}
