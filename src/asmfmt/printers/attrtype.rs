//!
//! Type and Attribute directives
//! ====================================
//!

use std::fmt;

use crate::{
    common_traits::Qualified,
    context::Context,
    printable::{Printable, State},
};

use super::PrinterFn;

#[macro_export]
macro_rules! at_params_directive {
    ($self:ident, ($($printer:ident),*), (), ($($params:ident)*)) => {
        concat_with_sep(
            ListSeparator::Char(','),
            ($(
                ::pliron::asmfmt::printers::print_var!(&$self.$params)
            ),*),
        ).fmt($($printer),*)?;
    };
    ($_self:ident, ($($_printer:ident),*), ($($_field_name:ident)+), ($($_param:ident)*)) => {
        compile_error!("params directive used with too many parameters");
    };
}
#[allow(unused_imports)]
pub(crate) use at_params_directive;

#[macro_export]
macro_rules! at_qualifier_directive {
    ($self:ident, ($($printer:ident),*), (), ($($_param:ident)*)) => {
        qualifier($self).fmt($($printer),*)?;
    };
    ($self:ident, ($($printer:ident),*), ($field_name:tt), ($($_param:ident)*)) => {
        qualifier(&$self.$field_name).fmt($($printer),*)?;
    };
}
#[allow(unused_imports)]
pub(crate) use at_qualifier_directive;

// Prints the qualifier o a qualified object like a type or an attribute.
pub fn qualifier<T>(v: &T) -> impl Printable + '_
where
    T: Qualified,
    <T as Qualified>::Qualifier: Printable,
{
    PrinterFn(
        move |ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>| {
            v.get_qualifier(ctx).fmt(ctx, state, f)
        },
    )
}

#[macro_export]
macro_rules! at_qualified_directive {
    ($self:ident, ($($_printer:ident),*), (), ($($_param:tt)*)) => {
        compile_error!("qualified directive used without parameter");
    };
    ($self:ident, ($($printer:ident),*), ($field_name:tt), ($($params:tt)*)) => {
        concat((qualifier(&$self.$field_name), " ", $self.$field_name)).fmt($($printer),*)?;
    };
    ($self:ident, ($($printer:ident),*), ($field_name:tt, $($extra:tt),+), ($($params:tt)*)) => {
        compile_error!("qualified directive used with too many field names");
    };
}
#[allow(unused_imports)]
pub(crate) use at_qualified_directive;

#[macro_export]
macro_rules! at_struct_directive {
    ($self:ident, ($($printer:ident),*), ($($field_name:tt),*), ($($_param:ident)*)) => {
        concat_with_sep(
            ::pliron::printable::ListSeparator::Char(','),
            ($(
              concat((
                literal(stringify!($field_name)),
                " = ",
                ::pliron::asmfmt::printers::print_var!(&$self.$field_name),
              ))
            ),*),
        ).fmt($($printer),*)?;
    };
}
#[allow(unused_imports)]
pub(crate) use at_struct_directive;

#[allow(unused_macros)]
macro_rules! at_format_directive {
    ($self:ident, ($($printer:ident),*), (), ($($_param:ident)*)) => {
        compile_error!("format directive used without parameter");
    };
    ($self:ident, ($($printer:ident),*), ($fmt:expr, $field_name:ident), ($($params:ident)*)) => {
        formatted(format!($fmt, $self.$field_name)).fmt($($printer),*)?;
    };
    ($self:ident, ($($printer:ident),*), ($fmt:expr, $field_name:ident, $($extra:ident),+), ($($params:ident)*)) => {
        compile_error!("format directive used with too many field names");
    };
}
#[allow(unused_imports)]
pub(crate) use at_format_directive;

#[macro_export]
macro_rules! at_quoted_directive {
    ($self:ident, ($($printer:ident),*), (), ($($_param:tt)*)) => {
        compile_error!("quoted directive used without parameter");
    };
    ($self:ident, ($($printer:ident),*), ($field_name:tt), ($($params:tt)*)) => {
        quoted(&$self.$field_name).fmt($($printer),*)?;
    };
    ($self:ident, ($($printer:ident),*), ($field_name:tt, $($extra:tt),+), ($($params:tt)*)) => {
        compile_error!("quoted directive used with too many field names");
    };
}
#[allow(unused_imports)]
pub(crate) use at_quoted_directive;
