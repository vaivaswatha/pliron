use crate::{
    basic_block::{BasicBlock, BlockArgument},
    context::{Context, Ptr},
    operation::{OpResult, Operation},
    use_def_lists::{DefRef, Use, UseRef},
};

// Container for a Def.
pub trait Value {
    // If this is an OpResult, return the defining Operation.
    fn get_defining_op(&self) -> Option<Ptr<Operation>>;
    // If this is a BlockArgument, or if the defining Operation is in a block.
    fn get_parent_block(&self) -> Option<Ptr<BasicBlock>>;
    // This definition is i'th result of the operation or i'th block argument.
    fn get_def_index(&self) -> usize;
    // Get this value's uses.
    fn get_uses(&self) -> &Vec<UseRef>;
    // Get this value's uses (mut).
    fn get_uses_mut(&mut self) -> &mut Vec<UseRef>;
    // Build a DefRef descriptor for this Value.
    fn build_defref(&self) -> DefRef;

    // Replace all uses of this value with @new_val.
    // When this fn finishes, self will not have any uses.
    fn replace_all_uses_with<T: Value>(&mut self, ctx: &mut Context, new_val: &mut T) {
        let new_defref = new_val.build_defref();
        let uses = self.get_uses_mut();
        for r#use in uses.iter() {
            let opd = r#use
                .op
                .deref_mut(ctx)
                .get_operand_mut(r#use.opd_idx)
                .unwrap();
            let new_val_uses = new_val.get_uses_mut();
            new_val_uses.push(opd.build_useref());
            opd.replace_use(Use {
                def: new_defref,
                use_idx: new_val_uses.len() - 1,
            });
        }
        // this Value just lost all its uses.
        uses.clear();
    }
}

// Container for a Use.
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
    pub fn replace_use(&mut self, r#use: Use) {
        self.r#use = r#use;
    }
}
