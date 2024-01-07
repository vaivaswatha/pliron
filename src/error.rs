//! Utilities for error handling

use thiserror::Error;

use crate::location::Location;

/// The kinds of errors we have during compilation.
#[derive(Debug, Error)]
pub enum ErrorKind {
    #[error("invalid input")]
    InvalidInput,
    #[error("verification failed")]
    VerificationFailed,
}

/// An error object that can hold any [std::error::Error].
#[derive(Debug, Error)]
#[error("Compilation error: {kind}.\n{err}")]
pub struct Error {
    pub kind: ErrorKind,
    pub err: Box<dyn std::error::Error + Send + Sync>,
    pub loc: Location,
}

/// Type alias for [std::result::Result] with the error type set to [struct@Error]
pub type Result<T> = std::result::Result<T, Error>;

#[doc(hidden)]
#[derive(Debug, Error)]
#[error("{0}")]
pub struct StringError(pub String);

/// Specify [ErrorKind] and create an error from any [std::error::Error] object.
/// The macro also accepts [format!] like arguments to create one-off errors.
/// It may be shorter to just use [verify_err!](crate::verify_err) or
/// [input_err!](crate::verify_err) instead.
#[macro_export]
macro_rules! create_err {
    ($kind: expr, $str: literal $($t:tt)*) => {
        $crate::create_err!($kind, $crate::error::StringError(format!($str $($t)*)))
    };
    ($kind: expr, $err: expr) => {
        Err($crate::error::Error {
            kind: $kind,
            err: Box::new($err),
            loc: $crate::location::Location::Unknown,
        })
    };
}

/// Create an [ErrorKind::VerificationFailed] error from any [std::error::Error] object.
/// The macro also accepts [format!] like arguments to create one-off errors.
/// ```rust
/// use thiserror::Error;
/// use pliron::{verify_err, error::{Result, ErrorKind, Error}};
///
/// #[derive(Error, Debug)]
/// #[error("sample error")]
/// pub struct SampleErr;
///
/// assert!(
///     matches!(
///         verify_err!(SampleErr),
///         Result::<()>::Err(Error {
///            kind: ErrorKind::VerificationFailed,
///            err,
///            loc: _,
///         }) if err.is::<SampleErr>()
/// ));
///
/// let res_msg: Result<()> = verify_err!("Some formatted {}", 0);
/// assert_eq!(
///     res_msg.unwrap_err().err.to_string(),
///     "Some formatted 0"
/// );
/// ```
#[macro_export]
macro_rules! verify_err {
    ($($t:tt)*) => {
        $crate::create_err!($crate::error::ErrorKind::VerificationFailed, $($t)*)
    }
}

/// Create an [ErrorKind::InvalidInput] error from any [std::error::Error] object.
/// The macro also accepts [format!] like arguments to create one-off errors.
/// ```rust
/// use thiserror::Error;
/// use pliron::{input_err, error::{Result, ErrorKind, Error}};
///
/// #[derive(Error, Debug)]
/// #[error("sample error")]
/// pub struct SampleErr;
///
/// assert!(
///     matches!(
///         input_err!(SampleErr),
///         Result::<()>::Err(Error {
///            kind: ErrorKind::InvalidInput,
///            err,
///            loc: _,
///         }) if err.is::<SampleErr>()
/// ));
///
/// let res_msg: Result<()> = input_err!("Some formatted {}", 0);
/// assert_eq!(
///     res_msg.unwrap_err().err.to_string(),
///     "Some formatted 0"
/// );
/// ```
#[macro_export]
macro_rules! input_err {
    ($($t:tt)*) => {
        $crate::create_err!($crate::error::ErrorKind::InvalidInput, $($t)*)
    }
}
