//! Utilities for attaching / retrieving debug info to / from the IR.

use std::collections::hash_map;

use rustc_hash::FxHashMap;

use crate::{
    attribute::AttrObj,
    basic_block::BasicBlock,
    context::{Context, Ptr},
    dialects::builtin::{
        attributes::{SmallDictAttr, StringAttr, UnitAttr, VecAttr},
        ATTR_KEY_DEBUG_INFO,
    },
    operation::Operation,
    vec_exns::VecExtns,
};

/// Key into a debug info's variable name.
const DEBUG_INFO_KEY_NAME: &str = "debug_info.name";

fn set_name_from_attr_map(
    attributes: &mut FxHashMap<&str, AttrObj>,
    idx: usize,
    max_idx: usize,
    name: String,
) {
    let name_attr = StringAttr::create(name);
    match attributes.entry(ATTR_KEY_DEBUG_INFO) {
        hash_map::Entry::Occupied(mut occupied) => {
            let di_dict = occupied.get_mut().downcast_mut::<SmallDictAttr>().unwrap();
            let expect_msg = "Existing attribute entry for result names incorrect";
            let names = di_dict
                .lookup_mut(DEBUG_INFO_KEY_NAME)
                .expect(expect_msg)
                .downcast_mut::<VecAttr>()
                .expect(expect_msg);
            names.0[idx] = name_attr;
        }
        hash_map::Entry::Vacant(vacant) => {
            let mut names = Vec::new_init(max_idx, |_idx| UnitAttr::create());
            names[idx] = name_attr;
            vacant.insert(SmallDictAttr::create(vec![(
                DEBUG_INFO_KEY_NAME,
                VecAttr::create(names),
            )]));
        }
    }
}

fn get_name_from_attr_map(
    attributes: &FxHashMap<&str, AttrObj>,
    idx: usize,
    panic_msg: &str,
) -> Option<String> {
    attributes.get(ATTR_KEY_DEBUG_INFO).and_then(|di_dict| {
        let di_dict = di_dict.downcast_ref::<SmallDictAttr>().expect(panic_msg);
        di_dict.lookup(DEBUG_INFO_KEY_NAME).and_then(|names| {
            let names = names.downcast_ref::<VecAttr>().expect(panic_msg);
            names.0.get(idx).and_then(|name| {
                name.downcast_ref::<StringAttr>()
                    .map(|name_attr| String::from(name_attr.clone()))
            })
        })
    })
}

/// Set the name for a result in an [Operation].
/// Panics if the given `res_idx` is out of range.
//  Names for the result are stored in an [Operation] as follows:
//      dict = op.attributes\[[ATTR_KEY_DEBUG_INFO]\] is a [SmallDictAttr]
//      dict\[[DEBUG_INFO_NAME]\] is a [VecAttr] with [UnitAttr] entries
//      for unknown names and [StringAttr] for known names. The length of
//      this array is always the same as the number of results.
pub fn set_operation_result_name(ctx: &Context, op: Ptr<Operation>, res_idx: usize, name: String) {
    let op = &mut *op.deref_mut(ctx);
    let num_results = op.get_num_results();
    assert!(res_idx < num_results);

    set_name_from_attr_map(&mut op.attributes, res_idx, num_results, name);
}

/// Get name for a result in an [Operation].
//  See [set_operation_result_name] for attribute storage convention.
pub fn get_operation_result_name(
    ctx: &Context,
    op: Ptr<Operation>,
    res_idx: usize,
) -> Option<String> {
    let op = &*op.deref(ctx);
    let expect_msg = "Incorrect attribute for result names";

    get_name_from_attr_map(&op.attributes, res_idx, expect_msg)
}

/// Set the name for an argumet in a [BasicBlock].
/// Panics if the given `arg_idx` is out of range.
//  Names for the arguments are stored in a [BasicBlock] as follows:
//      dict = block.attributes\[[ATTR_KEY_DEBUG_INFO]\] is a [SmallDictAttr]
//      dict\[[DEBUG_INFO_NAME]\] is a [VecAttr] with [UnitAttr] entries
//      for unknown names and [StringAttr] for known names. The length of
//      this array is always the same as the number of arguments.
pub fn set_block_arg_name(ctx: &Context, block: Ptr<BasicBlock>, arg_idx: usize, name: String) {
    let block = &mut *block.deref_mut(ctx);
    let num_args = block.get_num_arguments();
    assert!(arg_idx < num_args);

    set_name_from_attr_map(&mut block.attributes, arg_idx, num_args, name);
}

/// Get name for an argument in a [BasicBlock].
//  See [set_block_arg_name] for attribute storage convention.
pub fn get_block_arg_name(ctx: &Context, block: Ptr<BasicBlock>, arg_idx: usize) -> Option<String> {
    let block = &*block.deref(ctx);
    let expect_msg = "Incorrect attribute for block arg names";
    get_name_from_attr_map(&block.attributes, arg_idx, expect_msg)
}

#[cfg(test)]
mod tests {
    use crate::{
        basic_block::BasicBlock,
        common_traits::Verify,
        context::Context,
        debug_info::{get_block_arg_name, set_block_arg_name},
        dialects::{
            self,
            builtin::{
                attributes::IntegerAttr,
                ops::ConstantOp,
                types::{IntegerType, Signedness},
            },
        },
        error::Result,
        op::Op,
    };
    use apint::ApInt;

    use super::{get_operation_result_name, set_operation_result_name};

    #[test]
    fn test_op_result_name() -> Result<()> {
        let mut ctx = Context::new();
        dialects::builtin::register(&mut ctx);

        let i64_ty = IntegerType::get(&mut ctx, 64, Signedness::Signed);
        let cop = ConstantOp::new_unlinked(&mut ctx, IntegerAttr::create(i64_ty, ApInt::from(0)));
        let op = cop.get_operation();
        set_operation_result_name(&ctx, op, 0, "foo".to_string());
        assert!(get_operation_result_name(&ctx, op, 0).unwrap() == "foo");
        op.deref(&ctx).verify(&ctx)?;
        Ok(())
    }

    #[test]
    fn test_block_arg_name() -> Result<()> {
        let mut ctx = Context::new();
        dialects::builtin::register(&mut ctx);

        let i64_ty = IntegerType::get(&mut ctx, 64, Signedness::Signed);
        let block = BasicBlock::new(&mut ctx, Some("entry".into()), vec![i64_ty]);
        set_block_arg_name(&ctx, block, 0, "foo".to_string());
        assert!(get_block_arg_name(&ctx, block, 0).unwrap() == "foo");
        block.deref(&ctx).verify(&ctx)?;
        Ok(())
    }
}
