//! Utilities for attaching / retrieving debug info to / from the IR.

use std::collections::hash_map::Entry;

use crate::{
    attribute::{AttrObj, AttributeDict},
    basic_block::BasicBlock,
    builtin::{
        ATTR_KEY_DEBUG_INFO,
        attributes::{DictAttr, IdentifierAttr, UnitAttr, VecAttr},
    },
    context::{Context, Ptr},
    dict_key,
    identifier::Identifier,
    operation::Operation,
    utils::vec_exns::VecExtns,
};

dict_key!(
    /// Key into a debug info's variable name.
    DEBUG_INFO_KEY_NAME, "debug_info_name"
);

fn set_name_from_attr_map(
    attributes: &mut AttributeDict,
    idx: usize,
    max_idx: usize,
    name: Identifier,
) {
    let name_attr: AttrObj = IdentifierAttr::new(name).into();
    match attributes.0.entry(ATTR_KEY_DEBUG_INFO.clone()) {
        Entry::Occupied(mut occupied) => {
            let di_dict = occupied.get_mut().downcast_mut::<DictAttr>().unwrap();
            let expect_msg = "Existing attribute entry for result names incorrect";
            let names = di_dict
                .lookup_mut(&DEBUG_INFO_KEY_NAME)
                .expect(expect_msg)
                .downcast_mut::<VecAttr>()
                .expect(expect_msg);
            names.0[idx] = name_attr;
        }
        Entry::Vacant(vacant) => {
            let mut names = Vec::new_init(max_idx, |_idx| UnitAttr::new().into());
            names[idx] = name_attr;
            vacant.insert(
                DictAttr::new(vec![(
                    DEBUG_INFO_KEY_NAME.clone(),
                    VecAttr::new(names).into(),
                )])
                .into(),
            );
        }
    }
}

fn get_name_from_attr_map(
    attributes: &AttributeDict,
    idx: usize,
    panic_msg: &str,
) -> Option<Identifier> {
    attributes
        .get::<DictAttr>(&ATTR_KEY_DEBUG_INFO)
        .and_then(|di_dict| {
            di_dict.lookup(&DEBUG_INFO_KEY_NAME).and_then(|names| {
                let names = names.downcast_ref::<VecAttr>().expect(panic_msg);
                names.0.get(idx).and_then(|name| {
                    name.downcast_ref::<IdentifierAttr>()
                        .map(|name_attr| name_attr.clone().into())
                })
            })
        })
}

/// Set the name for a result in an [Operation].
/// Panics if the given `res_idx` is out of range.
//  Names for the result are stored in an [Operation] as follows:
//      dict = op.attributes\[[ATTR_KEY_DEBUG_INFO]\] is a [SmallDictAttr]
//      dict\[[DEBUG_INFO_NAME]\] is a [VecAttr] with [UnitAttr] entries
//      for unknown names and [IdentiferAttr] for known names. The length of
//      this array is always the same as the number of results.
pub fn set_operation_result_name(
    ctx: &Context,
    op: Ptr<Operation>,
    res_idx: usize,
    name: Identifier,
) {
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
) -> Option<Identifier> {
    let op = &*op.deref(ctx);
    let expect_msg = "Incorrect attribute for result names";

    get_name_from_attr_map(&op.attributes, res_idx, expect_msg)
}

/// Set the name for an argumet in a [BasicBlock].
/// Panics if the given `arg_idx` is out of range.
//  Names for the arguments are stored in a [BasicBlock] as follows:
//      dict = block.attributes\[[ATTR_KEY_DEBUG_INFO]\] is a [SmallDictAttr]
//      dict\[[DEBUG_INFO_NAME]\] is a [VecAttr] with [UnitAttr] entries
//      for unknown names and [IdentiferAttr] for known names. The length of
//      this array is always the same as the number of arguments.
pub fn set_block_arg_name(ctx: &Context, block: Ptr<BasicBlock>, arg_idx: usize, name: Identifier) {
    let block = &mut *block.deref_mut(ctx);
    let num_args = block.get_num_arguments();
    assert!(arg_idx < num_args);

    set_name_from_attr_map(&mut block.attributes, arg_idx, num_args, name);
}

/// Get name for an argument in a [BasicBlock].
//  See [set_block_arg_name] for attribute storage convention.
pub fn get_block_arg_name(
    ctx: &Context,
    block: Ptr<BasicBlock>,
    arg_idx: usize,
) -> Option<Identifier> {
    let block = &*block.deref(ctx);
    let expect_msg = "Incorrect attribute for block arg names";
    get_name_from_attr_map(&block.attributes, arg_idx, expect_msg)
}

#[cfg(test)]
mod tests {
    use pliron::derive::pliron_op;

    use crate::{
        basic_block::BasicBlock,
        builtin::{
            op_interfaces::{NOpdsInterface, NResultsInterface, OneResultInterface},
            types::{IntegerType, Signedness},
        },
        common_traits::Verify,
        context::Context,
        debug_info::{get_block_arg_name, set_block_arg_name},
        op::Op,
        operation::Operation,
        result::Result,
    };

    #[pliron_op(
        name = "test.zero"
        format
        interfaces = [
            OneResultInterface, NResultsInterface<1>, NOpdsInterface<0>
        ]
        verifier = "succ"
    )]
    struct ZeroOp;
    impl ZeroOp {
        pub fn new(ctx: &mut Context) -> Self {
            let i64_ty = IntegerType::get(ctx, 64, Signedness::Signed);
            ZeroOp {
                op: Operation::new(
                    ctx,
                    Self::get_concrete_op_info(),
                    vec![i64_ty.into()],
                    vec![],
                    vec![],
                    0,
                ),
            }
        }
    }

    use super::{get_operation_result_name, set_operation_result_name};

    #[test]
    fn test_op_result_name() -> Result<()> {
        let mut ctx = Context::new();
        let cop = ZeroOp::new(&mut ctx);
        let op = cop.get_operation();
        set_operation_result_name(&ctx, op, 0, "foo".try_into().unwrap());
        assert_eq!(
            get_operation_result_name(&ctx, op, 0).unwrap(),
            "foo".try_into().unwrap()
        );
        op.deref(&ctx).verify(&ctx)?;
        Ok(())
    }

    #[test]
    fn test_block_arg_name() -> Result<()> {
        let mut ctx = Context::new();
        let i64_ty = IntegerType::get(&mut ctx, 64, Signedness::Signed);
        let block = BasicBlock::new(
            &mut ctx,
            Some("entry".try_into().unwrap()),
            vec![i64_ty.into()],
        );
        set_block_arg_name(&ctx, block, 0, "foo".try_into().unwrap());
        assert!(get_block_arg_name(&ctx, block, 0).unwrap() == "foo".try_into().unwrap());
        Ok(())
    }
}
