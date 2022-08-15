use crate::{
    context::{ArenaObj, Context, Ptr, ArenaCell},
    operation::Operation,
    use_def_lists::{Def, DefRef, Use, UseRef},
    value::Value,
    vec_exns::VecExtns,
};

#[derive(Debug)]
pub struct BlockArgument {
    def: Def,
    def_block: Ptr<BasicBlock>,
    arg_idx: usize,
}

impl Value for BlockArgument {
    fn get_defining_op(&self) -> Option<Ptr<Operation>> {
        None
    }

    fn get_parent_block(&self, _ctx: &Context) -> Option<Ptr<BasicBlock>> {
        Some (self.def_block)
    }

    fn get_def_index(&self) -> usize {
        self.arg_idx
    }

    fn get_uses(&self) -> &Vec<UseRef> {
        &self.def.uses
    }

    fn get_uses_mut(&mut self) -> &mut Vec<UseRef> {
        &mut self.def.uses
    }

    fn add_use(&mut self, r#use: UseRef) -> Use {
        let use_idx = self.def.uses.push_back(r#use);
        Use {
            def: DefRef::BlockArgument {
                block: self.def_block,
                arg_idx: self.get_def_index(),
            },
            use_idx,
        }
    }
}

#[derive(Debug)]
pub struct BasicBlock {

}

impl ArenaObj for BasicBlock {
    fn get_arena(ctx: &Context) -> &ArenaCell<Self> {
        todo!()
    }
    fn get_arena_mut(ctx: &mut Context) -> &mut ArenaCell<Self> {
        todo!()
    }
    fn dealloc_sub_objects(ptr: Ptr<Self>, ctx: &mut Context) {
        todo!()
    }
    fn remove_references(ptr: Ptr<Self>, ctx: &mut Context) {
        todo!()
    }

    fn get_self_ptr(&self) -> Ptr<Self> {
        todo!()
    }
}
