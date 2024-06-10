use crate::{
    attribute::Attribute,
    context::{Context, Ptr},
    decl_attr_interface,
    r#type::TypeObj,
    result::Result,
};

decl_attr_interface! {
    /// [Attribute]s that have an associated [Type](crate::type::Type).
    /// This serves the same purpose as MLIR's `TypedAttrInterface`.
    TypedAttrInterface {
        /// Get this attribute's type.
        fn get_type(&self) -> Ptr<TypeObj>;

        fn verify(_attr: &dyn Attribute, _ctx: &Context) -> Result<()>
        where
            Self: Sized,
        {
            Ok(())
        }
    }
}
