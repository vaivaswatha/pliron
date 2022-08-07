use std::marker::PhantomData;

use generational_arena;

use crate::{
    basic_block::BasicBlock,
    context::{ArenaObj, Context, Ptr},
    use_def_lists::{Def, DefRef, Use, UseRef},
    value::Value,
    vec_exns::VecExtns,
};

#[derive(Debug)]
pub struct OpResult {
    def: Def,
    def_op: Ptr<Operation>,
    res_idx: usize,
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

    fn add_use(&mut self, r#use: UseRef) -> Use {
        let use_idx = self.def.uses.push_back(r#use);
        Use {
            def: DefRef::OpResult {
                op: self.get_defining_op().unwrap(),
                res_idx: self.get_def_index(),
            },
            use_idx,
        }
    }
}

#[derive(Debug)]
pub struct Operation {
    pub self_ptr: Ptr<Operation>,
    pub results: Vec<OpResult>,
    pub operands: Vec<Operand>,
}

impl Operation {
    pub fn new(ctx: &mut Context, num_results: usize, operands: Vec<DefRef>) -> Ptr<Operation> {
        let f = |self_ptr: Ptr<Operation>| Operation {
            self_ptr,
            results: Vec::new_init(num_results, |res_idx| OpResult {
                def: Def { uses: vec![] },
                def_op: self_ptr,
                res_idx,
            }),
            operands: vec![],
        };
        let newop = Self::alloc(ctx, f);
        let operands: Vec<Operand> = operands
            .iter()
            .enumerate()
            .map(|(opd_idx, def)| {
                let defval = def.get_value_ref_mut(ctx);
                let r#use = defval.add_use(UseRef { op: newop, opd_idx });
                Operand {
                    r#use,
                    opd_idx,
                    user_op: newop,
                }
            })
            .collect();
        newop.deref_mut(ctx).operands = operands;
        newop
    }
    pub fn get_result<'a>(&'a self, idx: usize) -> Option<&OpResult> {
        self.results.get(idx)
    }
    pub fn get_result_mut<'a>(&'a mut self, idx: usize) -> Option<&mut OpResult> {
        self.results.get_mut(idx)
    }
    pub fn get_operand(&self, opd_idx: usize) -> Option<&Operand> {
        self.operands.get(opd_idx)
    }
    pub fn get_operand_mut(&mut self, opd_idx: usize) -> Option<&mut Operand> {
        self.operands.get_mut(opd_idx)
    }
}

impl ArenaObj for Operation {
    fn get_arena(ctx: &Context) -> &generational_arena::Arena<Self> {
        &ctx.operations
    }
    fn get_arena_mut(ctx: &mut Context) -> &mut generational_arena::Arena<Self> {
        &mut ctx.operations
    }
    fn dealloc_sub_objects(ptr: Ptr<Self>, ctx: &mut Context) {
        todo!()
    }
    fn remove_references(ptr: Ptr<Self>, ctx: &mut Context) {
        todo!()
    }
}

// Container for a Use.
#[derive(Debug)]
pub struct Operand {
    r#use: Use,
    opd_idx: usize,
    user_op: Ptr<Operation>,
}

impl Operand {
    // i'th operand in the Operation that contains this.
    pub fn get_opd_idx(&self) -> usize {
        self.opd_idx
    }
    // Get the operation of which this is an operand.
    pub fn get_user_op(&self) -> Ptr<Operation> {
        self.user_op
    }
    // Build a UseRef referring to this operand.
    pub fn build_useref(&self) -> UseRef {
        UseRef {
            op: self.get_user_op(),
            opd_idx: self.get_opd_idx(),
        }
    }
    // Update the operand to be the Use of a different Def.
    pub fn replace_def(&mut self, new_val: Use) {
        self.r#use = new_val;
    }
}
