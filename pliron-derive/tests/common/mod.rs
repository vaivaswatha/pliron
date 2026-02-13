use pliron::{builtin::op_interfaces::IsTerminatorInterface, impl_verify_succ};
use pliron_derive::{def_op, derive_op_interface_impl, format_op};

#[def_op("test.return")]
#[format_op("$0")]
#[derive_op_interface_impl(IsTerminatorInterface)]
pub struct ReturnOp;
impl_verify_succ!(ReturnOp);
