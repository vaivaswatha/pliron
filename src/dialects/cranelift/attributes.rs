use cranelift_module::Linkage;
use pliron_derive::{def_attribute, NotParsable, Printable};

use crate::{
    attribute::{AttrObj, Attribute},
    common_traits::Verify,
    dialect::Dialect,
    parsable::Parsable,
};

pub fn register(dialect: &mut Dialect) {
    LinkageAttr::register_attr_in_dialect(dialect, LinkageAttr::parser_fn);
}

#[def_attribute("cranelift.linkage")]
#[derive(Debug, PartialEq, Eq, Clone, Printable, NotParsable)]
#[ir_format = "`<` format(`{:?}`,$linkage)  `>`"]
pub struct LinkageAttr {
    pub linkage: Linkage,
}
impl Verify for LinkageAttr {
    fn verify(&self, _ctx: &crate::context::Context) -> crate::error::Result<()> {
        Ok(())
    }
}

impl LinkageAttr {
    pub fn create(linkage: Linkage) -> AttrObj {
        Box::new(LinkageAttr { linkage })
    }
}
