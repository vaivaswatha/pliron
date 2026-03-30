//! Utilities for attaching / retrieving debug info to / from the IR.

use std::collections::hash_map::Entry;

use combine::{Parser, attempt, between, parser::char::spaces, sep_by, token};
use pliron::derive::pliron_attr;
use pliron_derive::attr_interface_impl;

use crate::{
    attribute::AttributeDict,
    basic_block::BasicBlock,
    builtin::{ATTR_KEY_DEBUG_INFO, attr_interfaces::OutlinedAttr},
    context::{Context, Ptr},
    identifier::Identifier,
    operation::Operation,
    parsable::{Parsable, ParseResult, StateStream},
    printable::{self, Printable},
};

#[pliron_attr(name = "builtin.debug_info", verifier = "succ")]
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct DebugInfoAttr {
    names: Vec<Option<Identifier>>,
}

impl DebugInfoAttr {
    fn new(size: usize) -> Self {
        Self {
            names: vec![None; size],
        }
    }

    fn get_name(&self, idx: usize) -> Option<Identifier> {
        self.names
            .get(idx)
            .expect("Index out of range for debug info attribute")
            .clone()
    }

    fn set_name(&mut self, idx: usize, name: Identifier) {
        *self
            .names
            .get_mut(idx)
            .expect("Index out of range for debug info attribute") = Some(name);
    }
}

#[attr_interface_impl]
impl OutlinedAttr for DebugInfoAttr {}

impl Printable for DebugInfoAttr {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &printable::State,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        write!(
            f,
            "[{}]",
            self.names
                .iter()
                .map(|name| match name {
                    Some(name) => name.disp(ctx).to_string(),
                    None => "?".to_string(),
                })
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

impl Parsable for DebugInfoAttr {
    type Arg = ();
    type Parsed = Self;

    fn parse<'a>(
        state_stream: &mut StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        between(
            token('[').skip(spaces()),
            spaces().with(token(']')),
            sep_by(
                attempt(token('?').map(|_| None)).or(Identifier::parser(()).map(Some)),
                token(',').skip(spaces()),
            ),
        )
        .map(|names| DebugInfoAttr { names })
        .parse_stream(state_stream)
        .into()
    }
}

fn set_name_from_attr_map(
    attributes: &mut AttributeDict,
    idx: usize,
    max_idx: usize,
    name: Identifier,
) {
    match attributes.0.entry(ATTR_KEY_DEBUG_INFO.clone()) {
        Entry::Occupied(mut occupied) => {
            let debug_info = occupied
                .get_mut()
                .downcast_mut::<DebugInfoAttr>()
                .expect("Existing attribute entry for debug info incorrect");
            debug_info.set_name(idx, name);
        }
        Entry::Vacant(vacant) => {
            let mut debug_info = DebugInfoAttr::new(max_idx);
            debug_info.set_name(idx, name);
            vacant.insert(debug_info.into());
        }
    }
}

fn get_name_from_attr_map(attributes: &AttributeDict, idx: usize) -> Option<Identifier> {
    attributes
        .get::<DebugInfoAttr>(&ATTR_KEY_DEBUG_INFO)
        .and_then(|debug_info| debug_info.get_name(idx))
}

/// Set the name for a result in an [Operation].
/// Panics if the given `res_idx` is out of range.
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
pub fn get_operation_result_name(
    ctx: &Context,
    op: Ptr<Operation>,
    res_idx: usize,
) -> Option<Identifier> {
    let op = &*op.deref(ctx);
    get_name_from_attr_map(&op.attributes, res_idx)
}

/// Set the name for an argumet in a [BasicBlock].
/// Panics if the given `arg_idx` is out of range.
pub fn set_block_arg_name(ctx: &Context, block: Ptr<BasicBlock>, arg_idx: usize, name: Identifier) {
    let block = &mut *block.deref_mut(ctx);
    let num_args = block.get_num_arguments();
    assert!(arg_idx < num_args);

    set_name_from_attr_map(&mut block.attributes, arg_idx, num_args, name);
}

/// Get name for an argument in a [BasicBlock].
pub fn get_block_arg_name(
    ctx: &Context,
    block: Ptr<BasicBlock>,
    arg_idx: usize,
) -> Option<Identifier> {
    let block = &*block.deref(ctx);
    get_name_from_attr_map(&block.attributes, arg_idx)
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
        name = "test.zero",
        format,
        interfaces = [
            OneResultInterface, NResultsInterface<1>, NOpdsInterface<0>
        ],
        verifier = "succ",
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
