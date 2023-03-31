//! Utilities for attaching / retrieving debug info to / from the IR.

use std::collections::hash_map;

use crate::{
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

/// Set the name for a result in an [Operation].
/// Panics if the given `res_idx` is out of range.
//  Names for the result are stored in an [Operation] as follows:
//      dict = op.attributes\[[ATTR_KEY_DEBUG_INFO]\] is a [SmallDictAttr]
//      dict\[[DEBUG_INFO_NAME]\] is a [VecAttr] with [UnitAttr] entries
//      for unknown names and [StringAttr] for known names. The length of
//      this array is always the same as the number of results.
pub fn set_operation_result_name(
    ctx: &mut Context,
    op: Ptr<Operation>,
    res_idx: usize,
    name: String,
) {
    let op = &mut *op.deref_mut(ctx);
    let num_results = op.get_num_results();
    assert!(res_idx < num_results);

    let name_attr = StringAttr::create(name);
    match op.attributes.entry(ATTR_KEY_DEBUG_INFO) {
        hash_map::Entry::Occupied(mut occupied) => {
            let di_dict = occupied.get_mut().downcast_mut::<SmallDictAttr>().unwrap();
            let expect_msg = "Existing attribute entry for result names incorrect";
            let names = di_dict
                .lookup_mut(DEBUG_INFO_KEY_NAME)
                .expect(expect_msg)
                .downcast_mut::<VecAttr>()
                .expect(expect_msg);
            names.0[res_idx] = name_attr;
        }
        hash_map::Entry::Vacant(vacant) => {
            let mut names = Vec::new_init(num_results, |_idx| UnitAttr::create());
            names[res_idx] = name_attr;
            vacant.insert(SmallDictAttr::create(vec![(
                DEBUG_INFO_KEY_NAME,
                VecAttr::create(names),
            )]));
        }
    }
}

/// Get name for a result in an [Operation].
//  See [get_operation_result_name] for attribute storage convention.
pub fn get_operation_result_name(
    ctx: &Context,
    op: Ptr<Operation>,
    res_idx: usize,
) -> Option<String> {
    let op = &*op.deref_mut(ctx);
    let expect_msg = "Incorrect attribute for result names";

    op.attributes.get(ATTR_KEY_DEBUG_INFO).and_then(|di_dict| {
        let di_dict = di_dict.downcast_ref::<SmallDictAttr>().expect(expect_msg);
        di_dict.lookup(DEBUG_INFO_KEY_NAME).and_then(|names| {
            let names = names.downcast_ref::<VecAttr>().expect(expect_msg);
            names.0.get(res_idx).and_then(|name| {
                name.downcast_ref::<StringAttr>()
                    .map(|name_attr| String::from(name_attr.clone()))
            })
        })
    })
}

#[cfg(test)]
mod tests {
    use apint::ApInt;

    use crate::{
        context::Context,
        dialects::builtin::{attributes::IntegerAttr, ops::ConstantOp},
        op::Op,
    };

    use super::{get_operation_result_name, set_operation_result_name};

    #[test]
    fn test_op_result_name() {
        let mut ctx = Context::new();

        let cop = ConstantOp::new_unlinked(&mut ctx, IntegerAttr::create(ApInt::from(0)));
        let op = cop.get_operation();
        set_operation_result_name(&mut ctx, op, 0, "foo".to_string());
        assert!(get_operation_result_name(&ctx, op, 0).unwrap() == "foo");
    }
}
