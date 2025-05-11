//! Utilities for error handling

use std::{
    backtrace::{Backtrace, BacktraceStatus},
    fmt::Display,
};

use downcast_rs::{DowncastSync, impl_downcast};
use thiserror::Error;

use crate::{
    context::Context,
    location::{Located, Location},
    printable::{Printable, State},
    type_to_trait, utils,
};

/// The kinds of errors we have during compilation.
#[derive(Debug, Error)]
pub enum ErrorKind {
    /// Something's wrong with the program being compiled
    #[error("invalid input program")]
    InvalidInput,
    /// The IR was found to be inconsistent or invalid during verification
    #[error("verification failed")]
    VerificationFailed,
    /// Inconsistent or invalid argument(s) passed to a pliron function.
    #[error("invalid argument")]
    InvalidArgument,
}

/// An error object that can hold any [std::error::Error].
#[derive(Debug)]
pub struct Error {
    /// The kind of error this is
    pub kind: ErrorKind,
    /// The actual error object describing the error
    pub err: Box<dyn PlironError>,
    /// Location of this error in the code being compiled
    pub loc: Location,
    /// Details of how this error occurred
    pub backtrace: Backtrace,
}

/// This does not print [Location] or [Backtrace]. Use [Printable::disp] for that.
impl Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Compilation error: {}.\n{}", self.kind, self.err)
    }
}

pub trait PlironError: std::error::Error + DowncastSync {}

impl<T: std::error::Error + Send + Sync + 'static> PlironError for T {}

crate::impl_printable_for_display!(dyn PlironError);
impl_downcast!(PlironError);

impl std::error::Error for Error {}

impl Printable for Error {
    fn fmt(
        &self,
        ctx: &Context,
        _state: &State,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        writeln!(
            f,
            "[{}] Compilation error: {}.",
            self.loc.disp(ctx),
            self.kind,
        )?;

        let any_ref = (*self.err).as_any();

        type_to_trait!(&dyn PlironError, Printable);

        if let Some(self_val) = utils::trait_cast::any_to_trait::<dyn Printable>(any_ref) {
            write!(f, "{}", self_val.disp(ctx))?;
        } else if let Some(self_val) = self.err.downcast_ref::<Error>() {
            write!(f, "{}", self_val.disp(ctx))?;
        } else {
            write!(f, "{}", self.err)?;
            if self.backtrace.status() == BacktraceStatus::Captured {
                write!(f, "\nError backtrace:\n{}", self.backtrace)?;
            }
        }

        Ok(())
    }
}

impl Located for Error {
    fn loc(&self) -> Location {
        self.loc.clone()
    }

    fn set_loc(&mut self, loc: Location) {
        self.loc = loc;
    }
}

/// Type alias for [std::result::Result] with the error type set to [struct@Error]
pub type Result<T> = std::result::Result<T, Error>;

#[doc(hidden)]
#[derive(Debug, Error)]
#[error("{0}")]
pub struct StringError(pub String);

/// Specify [ErrorKind] and create [struct@Error] from any [std::error::Error] object.
/// To create [Result], use [create_err!](crate::create_err) instead.
/// The macro also accepts [format!] like arguments to create one-off errors.
/// It may be shorter to just use [verify_error!](crate::verify_error),
/// [input_error!](crate::input_error) or [arg_error!](crate::arg_error) instead.
#[macro_export]
macro_rules! create_error {
    ($loc: expr, $kind: expr, $str: literal $($t:tt)*) => {
        $crate::create_error!($loc, $kind, $crate::result::StringError(format!($str $($t)*)))
    };
    ($loc: expr, $kind: expr, $err: expr) => {
        $crate::result::Error {
            kind: $kind,
            err: Box::new($err),
            loc: $loc,
            backtrace: std::backtrace::Backtrace::capture(),
        }
    };
}

/// Specify [ErrorKind] and create [Result] from any [std::error::Error] object.
/// To create [struct@Error], use [create_error!](crate::create_error) instead.
/// The macro also accepts [format!] like arguments to create one-off errors.
/// It may be shorter to just use [verify_err!](crate::verify_err),
/// [input_err!](crate::input_err) or [arg_err!](crate::arg_err) instead.
#[macro_export]
macro_rules! create_err {
    ($loc: expr, $kind: expr, $str: literal $($t:tt)*) => {
        $crate::create_err!($loc, $kind, $crate::result::StringError(format!($str $($t)*)))
    };
    ($loc: expr, $kind: expr, $err: expr) => {
        Err($crate::create_error!($loc, $kind, $err))
    };
}

// Create [ErrorKind::VerificationFailed] [struct@Error] from any [std::error::Error] object.
/// To create [Result], use [verify_err!](crate::verify_err) instead.
/// The macro also accepts [format!] like arguments to create one-off errors.
/// ```rust
/// use thiserror::Error;
/// use pliron::{verify_error, result::{Result, ErrorKind, Error}, location::Location};
///
/// #[derive(Error, Debug)]
/// #[error("sample error")]
/// pub struct SampleErr;
///
/// assert!(
///     matches!(
///         verify_error!(Location::Unknown, SampleErr),
///         Error {
///            kind: ErrorKind::VerificationFailed,
///            err,
///            ..
///         } if err.is::<SampleErr>()
/// ));
///
/// let res_msg: Error = verify_error!(Location::Unknown, "Some formatted {}", 0);
/// assert_eq!(
///     res_msg.err.to_string(),
///     "Some formatted 0"
/// );
/// ```
#[macro_export]
macro_rules! verify_error {
    ($loc: expr, $($t:tt)*) => {
        $crate::create_error!($loc, $crate::result::ErrorKind::VerificationFailed, $($t)*)
    }
}

/// Create [ErrorKind::VerificationFailed] [Result] from any [std::error::Error] object.
/// To create [struct@Error], use [verify_error!](crate::verify_error) instead.
/// The macro also accepts [format!] like arguments to create one-off errors.
/// ```rust
/// use thiserror::Error;
/// use pliron::{verify_err, result::{Result, ErrorKind, Error}, location::Location};
///
/// #[derive(Error, Debug)]
/// #[error("sample error")]
/// pub struct SampleErr;
///
/// assert!(
///     matches!(
///         verify_err!(Location::Unknown, SampleErr),
///         Result::<()>::Err(Error {
///            kind: ErrorKind::VerificationFailed,
///            err,
///            ..
///         }) if err.is::<SampleErr>()
/// ));
///
/// let res_msg: Result<()> = verify_err!(Location::Unknown, "Some formatted {}", 0);
/// assert_eq!(
///     res_msg.unwrap_err().err.to_string(),
///     "Some formatted 0"
/// );
/// ```
#[macro_export]
macro_rules! verify_err {
    ($loc: expr, $($t:tt)*) => {
        $crate::create_err!($loc, $crate::result::ErrorKind::VerificationFailed, $($t)*)
    }
}

/// Create [ErrorKind::InvalidInput] [struct@Error] from any [std::error::Error] object.
/// To create [Result], use [input_err!](crate::input_err) instead.
/// The macro also accepts [format!] like arguments to create one-off errors.
/// ```rust
/// use thiserror::Error;
/// use pliron::{input_error, result::{Result, ErrorKind, Error}, location::Location};
///
/// #[derive(Error, Debug)]
/// #[error("sample error")]
/// pub struct SampleErr;
///
/// assert!(
///     matches!(
///         input_error!(Location::Unknown, SampleErr),
///         Error {
///            kind: ErrorKind::InvalidInput,
///            err,
///            ..
///         } if err.is::<SampleErr>()
/// ));
///
/// let res_msg: Error = input_error!(Location::Unknown, "Some formatted {}", 0);
/// assert_eq!(
///     res_msg.err.to_string(),
///     "Some formatted 0"
/// );
/// ```
#[macro_export]
macro_rules! input_error {
    ($loc: expr, $($t:tt)*) => {
        $crate::create_error!($loc, $crate::result::ErrorKind::InvalidInput, $($t)*)
    }
}

/// Create [ErrorKind::InvalidInput] [Result] from any [std::error::Error] object.
/// To create [struct@Error], use [input_error!](crate::input_error) instead.
/// The macro also accepts [format!] like arguments to create one-off errors.
/// ```rust
/// use thiserror::Error;
/// use pliron::{input_err, result::{Result, ErrorKind, Error}, location::Location};
///
/// #[derive(Error, Debug)]
/// #[error("sample error")]
/// pub struct SampleErr;
///
/// assert!(
///     matches!(
///         input_err!(Location::Unknown, SampleErr),
///         Result::<()>::Err(Error {
///            kind: ErrorKind::InvalidInput,
///            err,
///            ..
///         }) if err.is::<SampleErr>()
/// ));
///
/// let res_msg: Result<()> = input_err!(Location::Unknown, "Some formatted {}", 0);
/// assert_eq!(
///     res_msg.unwrap_err().err.to_string(),
///     "Some formatted 0"
/// );
/// ```
#[macro_export]
macro_rules! input_err {
    ($loc: expr, $($t:tt)*) => {
        $crate::create_err!($loc, $crate::result::ErrorKind::InvalidInput, $($t)*)
    }
}

/// Create [ErrorKind::InvalidArgument] [struct@Error] from any [std::error::Error] object.
/// To create [Result], use [arg_err!](crate::arg_err) instead.
/// The macro also accepts [format!] like arguments to create one-off errors.
/// ```rust
/// use thiserror::Error;
/// use pliron::{arg_error, result::{Result, ErrorKind, Error}, location::Location};
///
/// #[derive(Error, Debug)]
/// #[error("sample error")]
/// pub struct SampleErr;
///
/// assert!(
///     matches!(
///         arg_error!(Location::Unknown, SampleErr),
///         Error {
///            kind: ErrorKind::InvalidArgument,
///            err,
///            ..
///         } if err.is::<SampleErr>()
/// ));
///
/// let res_msg: Error = arg_error!(Location::Unknown, "Some formatted {}", 0);
/// assert_eq!(
///     res_msg.err.to_string(),
///     "Some formatted 0"
/// );
/// ```
#[macro_export]
macro_rules! arg_error {
    ($loc: expr, $($t:tt)*) => {
        $crate::create_error!($loc, $crate::result::ErrorKind::InvalidArgument, $($t)*)
    }
}

/// Create [ErrorKind::InvalidArgument] [Result] from any [std::error::Error] object.
/// To create [struct@Error], use [arg_error!](crate::arg_error) instead.
/// The macro also accepts [format!] like arguments to create one-off errors.
/// ```rust
/// use thiserror::Error;
/// use pliron::{arg_err, result::{Result, ErrorKind, Error}, location::Location};
///
/// #[derive(Error, Debug)]
/// #[error("sample error")]
/// pub struct SampleErr;
///
/// assert!(
///     matches!(
///         arg_err!(Location::Unknown, SampleErr),
///         Result::<()>::Err(Error {
///            kind: ErrorKind::InvalidArgument,
///            err,
///            ..
///         }) if err.is::<SampleErr>()
/// ));
///
/// let res_msg: Result<()> = arg_err!(Location::Unknown, "Some formatted {}", 0);
/// assert_eq!(
///     res_msg.unwrap_err().err.to_string(),
///     "Some formatted 0"
/// );
/// ```
#[macro_export]
macro_rules! arg_err {
    ($loc: expr, $($t:tt)*) => {
        $crate::create_err!($loc, $crate::result::ErrorKind::InvalidArgument, $($t)*)
    }
}

/// Same as [verify_error] but when no location is known.
#[macro_export]
macro_rules! verify_error_noloc {
    ($($t:tt)*) => {
        $crate::create_error!($crate::location::Location::Unknown, $crate::result::ErrorKind::VerificationFailed, $($t)*)
    }
}

/// Same as [verify_err] but when no location is known.
#[macro_export]
macro_rules! verify_err_noloc {
    ($($t:tt)*) => {
        $crate::create_err!($crate::location::Location::Unknown, $crate::result::ErrorKind::VerificationFailed, $($t)*)
    }
}

/// Same as [input_error] but when no location is known.
#[macro_export]
macro_rules! input_error_noloc {
    ($($t:tt)*) => {
        $crate::create_error!($crate::location::Location::Unknown, $crate::result::ErrorKind::InvalidInput, $($t)*)
    }
}

/// Same as [input_err] but when no location is known.
#[macro_export]
macro_rules! input_err_noloc {
    ($($t:tt)*) => {
        $crate::create_err!($crate::location::Location::Unknown, $crate::result::ErrorKind::InvalidInput, $($t)*)
    }
}

/// Same as [arg_error] but when no location is known.
#[macro_export]
macro_rules! arg_error_noloc {
    ($($t:tt)*) => {
        $crate::create_error!($crate::location::Location::Unknown, $crate::result::ErrorKind::InvalidArgument, $($t)*)
    }
}

/// Same as [arg_err] but when no location is known.
#[macro_export]
macro_rules! arg_err_noloc {
    ($($t:tt)*) => {
        $crate::create_err!($crate::location::Location::Unknown, $crate::result::ErrorKind::InvalidArgument, $($t)*)
    }
}

#[cfg(test)]
mod tests {

    use combine::stream::position::{Positioner, SourcePosition};
    use expect_test::expect;
    use thiserror::Error;

    use crate::{
        context::Context,
        location::{Location, Source},
        printable::Printable,
    };

    #[derive(Debug, Error)]
    #[error("Test error")]
    pub struct TestErr;

    #[test]
    fn wrapped_err() {
        let ctx = &mut Context::new();
        let src = Source::new_from_file(ctx, "/tmp/test.pliron".into());

        let pos1 = SourcePosition::default();
        let loc1 = Location::SrcPos { src, pos: pos1 };

        let mut pos2 = SourcePosition::default();
        pos2.update(&' ');
        let loc2 = Location::SrcPos { pos: pos2, src };

        let res = input_error!(loc2, TestErr);
        let wrapped_res = input_error!(loc1, res);
        let expected_err_msg = expect![[r#"
            [/tmp/test.pliron: line: 1, column: 1] Compilation error: invalid input program.
            [/tmp/test.pliron: line: 1, column: 2] Compilation error: invalid input program.
            Test error"#]];

        let actual_err = wrapped_res.disp(ctx).to_string();
        expected_err_msg.assert_eq(&actual_err);
    }
}
