//! Utilities for attaching / retrieving debug info to / from the IR.

use std::{collections::hash_map, sync::LazyLock};

use crate::{
    attribute::{AttrObj, AttributeDict},
    basic_block::BasicBlock,
    builtin::{
        ATTR_KEY_DEBUG_INFO,
        attributes::{DictAttr, IdentifierAttr, UnitAttr, VecAttr},
    },
    context::{Context, Ptr},
    identifier::Identifier,
    operation::Operation,
    utils::vec_exns::VecExtns,
};

/// Key into a debug info's variable name.
pub static DEBUG_INFO_KEY_NAME: LazyLock<Identifier> =
    LazyLock::new(|| "debug_info_name".try_into().unwrap());

fn set_name_from_attr_map(
    attributes: &mut AttributeDict,
    idx: usize,
    max_idx: usize,
    name: Identifier,
) {
    let name_attr: AttrObj = IdentifierAttr::new(name).into();
    match attributes.0.entry(ATTR_KEY_DEBUG_INFO.clone()) {
        hash_map::Entry::Occupied(mut occupied) => {
            let di_dict = occupied.get_mut().downcast_mut::<DictAttr>().unwrap();
            let expect_msg = "Existing attribute entry for result names incorrect";
            let names = di_dict
                .lookup_mut(&DEBUG_INFO_KEY_NAME)
                .expect(expect_msg)
                .downcast_mut::<VecAttr>()
                .expect(expect_msg);
            names.0[idx] = name_attr;
        }
        hash_map::Entry::Vacant(vacant) => {
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

fn name_from_attr_map(
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
    let num_results = op.num_results();
    assert!(res_idx < num_results);

    set_name_from_attr_map(&mut op.attributes, res_idx, num_results, name);
}

/// Get name for a result in an [Operation].
//  See [set_operation_result_name] for attribute storage convention.
pub fn operation_result_name(
    ctx: &Context,
    op: Ptr<Operation>,
    res_idx: usize,
) -> Option<Identifier> {
    let op = &*op.deref(ctx);
    let expect_msg = "Incorrect attribute for result names";

    name_from_attr_map(&op.attributes, res_idx, expect_msg)
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
    let num_args = block.num_arguments();
    assert!(arg_idx < num_args);

    set_name_from_attr_map(&mut block.attributes, arg_idx, num_args, name);
}

/// Get name for an argument in a [BasicBlock].
//  See [set_block_arg_name] for attribute storage convention.
pub fn block_arg_name(ctx: &Context, block: Ptr<BasicBlock>, arg_idx: usize) -> Option<Identifier> {
    let block = &*block.deref(ctx);
    let expect_msg = "Incorrect attribute for block arg names";
    name_from_attr_map(&block.attributes, arg_idx, expect_msg)
}

#[cfg(test)]
mod tests {
    use pliron::derive::{def_op, derive_op_interface_impl};

    use crate::{
        basic_block::BasicBlock,
        builtin::{
            self,
            op_interfaces::{OneResultInterface, ZeroOpdInterface},
            types::{IntegerType, Signedness},
        },
        common_traits::Verify,
        context::Context,
        debug_info::{block_arg_name, set_block_arg_name},
        dialect::{Dialect, DialectName},
        impl_canonical_syntax, impl_verify_succ,
        op::Op,
        operation::Operation,
        parsable::Parsable,
        result::Result,
    };

    #[def_op("test.zero")]
    #[derive_op_interface_impl(ZeroOpdInterface, OneResultInterface)]
    struct ZeroOp;
    impl_canonical_syntax!(ZeroOp);
    impl_verify_succ!(ZeroOp);
    impl ZeroOp {
        pub fn new(ctx: &mut Context) -> Self {
            let i64_ty = IntegerType::get(ctx, 64, Signedness::Signed);
            ZeroOp {
                op: Operation::new(
                    ctx,
                    Self::opid_static(),
                    vec![i64_ty.into()],
                    vec![],
                    vec![],
                    0,
                ),
            }
        }
    }

    use super::{operation_result_name, set_operation_result_name};

    #[test]
    fn test_op_result_name() -> Result<()> {
        let mut ctx = Context::new();
        let test_dialect = Dialect::new(DialectName::new("test"));
        test_dialect.register(&mut ctx);
        ZeroOp::register(&mut ctx, ZeroOp::parser_fn);

        let cop = ZeroOp::new(&mut ctx);
        let op = cop.operation();
        set_operation_result_name(&ctx, op, 0, "foo".try_into().unwrap());
        assert_eq!(
            operation_result_name(&ctx, op, 0).unwrap(),
            "foo".try_into().unwrap()
        );
        op.deref(&ctx).verify(&ctx)?;
        Ok(())
    }

    #[test]
    fn test_block_arg_name() -> Result<()> {
        let mut ctx = Context::new();
        builtin::register(&mut ctx);

        let i64_ty = IntegerType::get(&mut ctx, 64, Signedness::Signed);
        let block = BasicBlock::new(
            &mut ctx,
            Some("entry".try_into().unwrap()),
            vec![i64_ty.into()],
        );
        set_block_arg_name(&ctx, block, 0, "foo".try_into().unwrap());
        assert!(block_arg_name(&ctx, block, 0).unwrap() == "foo".try_into().unwrap());
        block.deref(&ctx).verify(&ctx)?;
        Ok(())
    }
}
