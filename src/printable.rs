//! IR objects that are to be printed must implement [Printable].

use std::{
    cell::RefCell,
    fmt::{self, Display},
    rc::Rc,
};

use crate::{common_traits::RcSharable, context::Context};

#[derive(Clone)]
struct StateInner {
    // Number of spaces per indentation
    indent_width: u16,
    // Current indentation
    cur_indent: u16,
}

impl Default for StateInner {
    fn default() -> Self {
        Self {
            indent_width: 2,
            cur_indent: 0,
        }
    }
}

/// A light weight reference counted wrapper around a state for [Printable].
#[derive(Default)]
pub struct State(Rc<RefCell<StateInner>>);

impl State {
    /// Number of spaces per indentation
    pub fn get_indent_width(&self) -> u16 {
        self.0.as_ref().borrow().indent_width
    }

    /// Set the current indentation width
    pub fn set_indent_width(&self, indent_width: u16) {
        self.0.as_ref().borrow_mut().indent_width = indent_width;
    }

    /// What's the indentation we're at right now?
    pub fn get_current_indent(&self) -> u16 {
        self.0.as_ref().borrow().cur_indent
    }

    /// Increase the current indentation by [Self::get_indent_width]
    pub fn push_indent(&self) {
        let mut inner = self.0.as_ref().borrow_mut();
        inner.cur_indent += inner.indent_width;
    }
    /// Decrease the current indentation by [Self::get_indent_width].
    pub fn pop_indent(&self) {
        let mut inner = self.0.as_ref().borrow_mut();
        inner.cur_indent -= inner.indent_width;
    }
}

impl RcSharable for State {
    /// Light weight (reference counted) clone.
    fn share(&self) -> Self {
        State(self.0.clone())
    }

    /// New copy that doesn't share the internal state of self.
    fn replicate(&self) -> Self {
        State(Rc::new(RefCell::new(self.0.borrow().clone())))
    }
}

/// All statements in the block are indented during [fmt](Printable::fmt).
/// Simply wraps the block with [State::push_indent] and [State::pop_indent].
///
/// See [Printable] for example usage.
#[macro_export]
macro_rules! indented_block {
    ($state:ident, { $($tt:tt)* }) => {
        $state.push_indent();
        $($tt)*
        $state.pop_indent();
    }
}

/// An object that implements [Display].
struct Displayable<'t, 'c, T: Printable + ?Sized> {
    t: &'t T,
    ctx: &'c Context,
    state: State,
}

impl<T: Printable + ?Sized> Display for Displayable<'_, '_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.t.fmt(self.ctx, &self.state, f)
    }
}

/// Easy printing of IR objects.
///
/// [disp](Self::disp) calls [print](Self::print) with a default [State],
/// but otherwise, are both equivalent.
///
/// Example:
/// ```
/// use pliron::{context::Context, printable::{State, Printable, ListSeparator}};
/// use std::fmt;
/// struct S {
///     i: i64,
/// }
/// impl Printable for S {
///     fn fmt(&self, _ctx: &Context, _state: &State, f: &mut fmt::Formatter<'_>)
///     -> fmt::Result
///     {
///         write!(f, "{}", self.i)
///     }
/// }
///
/// let ctx = Context::new();
/// assert!(S { i: 108 }.disp(&ctx).to_string() == "108");
/// let state = State::default();
/// assert!(S { i: 0 }.print(&ctx, &state).to_string() == "0");
/// let svec = vec![ S { i: 8 }, S { i: 16 } ];
/// use pliron::{indented_block, printable::indented_nl};
/// indented_block!(state, {
///     assert_eq!(format!("{}{}", indented_nl(&state), S { i: 108 }.print(&ctx, &state)), "\n  108");
/// });
/// ```
pub trait Printable {
    fn fmt(&self, ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>) -> fmt::Result;

    /// Get a [Display]'able object from the given [Context] and default [State].
    fn disp<'t, 'c>(&'t self, ctx: &'c Context) -> Box<dyn Display + 'c>
    where
        't: 'c,
    {
        self.print(ctx, &State::default())
    }

    /// Get a [Display]'able object from the given [Context] and [State].
    fn print<'t, 'c>(&'t self, ctx: &'c Context, state: &State) -> Box<dyn Display + 'c>
    where
        't: 'c,
    {
        Box::new(Displayable {
            t: self,
            ctx,
            state: state.share(),
        })
    }
}
/// Implement [Printable] for a type that already implements [Display].
/// Example:
/// ```
///     struct MyType;
///     impl std::fmt::Display for MyType {
///         fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
///             write!(f, "{}", self)
///         }
///     }
///     pliron::impl_printable_for_display!(MyType);
/// ```
#[macro_export]
macro_rules! impl_printable_for_display {
    ($ty_name:ty) => {
        impl $crate::printable::Printable for $ty_name {
            fn fmt(
                &self,
                _ctx: &pliron::context::Context,
                _state: &pliron::printable::State,
                f: &mut std::fmt::Formatter<'_>,
            ) -> std::fmt::Result {
                write!(f, "{}", self)
            }
        }
    };
}

impl_printable_for_display!(&str);
impl_printable_for_display!(String);
impl_printable_for_display!(usize);
impl_printable_for_display!(u64);
impl_printable_for_display!(u32);

impl<T: Printable + ?Sized> Printable for &T {
    fn fmt(&self, ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        (*self).fmt(ctx, state, f)
    }
}

#[derive(Clone, Copy)]
/// When printing lists, how must they be separated
pub enum ListSeparator {
    /// No separator
    None,
    /// Newline
    Newline,
    /// Character followed by a newline.
    CharNewline(char),
    /// Single character
    Char(char),
    /// Single character followed by a space
    CharSpace(char),
}

impl Printable for ListSeparator {
    fn fmt(&self, _ctx: &Context, state: &State, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ListSeparator::None => Ok(()),
            ListSeparator::Newline => fmt_indented_newline(state, f),
            ListSeparator::CharNewline(c) => {
                write!(f, "{}", c)?;
                fmt_indented_newline(state, f)
            }
            ListSeparator::Char(c) => write!(f, "{}", c),
            ListSeparator::CharSpace(c) => write!(f, "{} ", c),
        }
    }
}

/// Iterate over [Item](Iterator::Item)s in an [Iterator] and print them.
pub fn fmt_iter<I>(
    mut iter: I,
    ctx: &Context,
    state: &State,
    sep: ListSeparator,
    f: &mut fmt::Formatter<'_>,
) -> fmt::Result
where
    I: Iterator,
    I::Item: Printable,
{
    if let Some(first) = iter.next() {
        first.fmt(ctx, state, f)?;
    }
    for item in iter {
        sep.fmt(ctx, state, f)?;
        item.fmt(ctx, state, f)?;
    }
    Ok(())
}

/// Print a new line followed by indentation as per current state.
pub fn fmt_indented_newline(state: &State, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let align = state.get_current_indent().into();
    write!(f, "\n{:>align$}", "")?;
    Ok(())
}

struct IndentedNewliner {
    state: State,
}

impl Display for IndentedNewliner {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_indented_newline(&self.state, f)
    }
}

/// Print a new line followed by indentation as per current state.
pub fn indented_nl(state: &State) -> impl Display {
    IndentedNewliner {
        state: state.share(),
    }
}

#[cfg(test)]
mod test {
    use crate::common_traits::RcSharable;

    use super::State;

    #[test]
    fn test_state_cloning() {
        let state = State::default();
        let cur_indent = state.get_current_indent();
        state.push_indent();
        assert!(cur_indent < state.get_current_indent());
        let state_new = state.replicate();
        state.pop_indent();
        assert!(state_new.get_current_indent() != state.get_current_indent());
        let state_new_2 = state_new.share();
        state_new_2.push_indent();
        assert!(state_new.get_current_indent() == state_new_2.get_current_indent());
    }
}
