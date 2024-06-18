//! [Identifier]s are strings used to name entities in programming languages.

use std::{fmt::Display, ops::Deref};

use combine::{token, Parser};
use thiserror::Error;

use crate::{
    context::Context,
    parsable::{self, Parsable, ParseResult},
    printable::{self, Printable},
    result::{self, Result},
    verify_err_noloc,
};

#[derive(Clone, Hash, PartialEq, Eq, Debug)]
/// An [Identifier] must satisfy the regex `[a-zA-Z_][a-zA-Z0-9_]*`.
/// Also see [module description](module@crate::identifier).
pub struct Identifier(String);

impl Identifier {
    /// Attempt to construct a new [Identifier] from a [String].
    pub fn try_new(value: String) -> Result<Self> {
        let re = regex::Regex::new(r"[a-zA-Z_][a-zA-Z0-9_]*").unwrap();
        if !(re.is_match(&value)) {
            return verify_err_noloc!(MalformedIdentifierErr(value.clone()));
        }
        Ok(Identifier(value))
    }
}

impl Printable for Identifier {
    fn fmt(
        &self,
        _ctx: &Context,
        _state: &printable::State,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        <Self as Display>::fmt(self, f)
    }
}

impl Display for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl TryFrom<String> for Identifier {
    type Error = result::Error;

    fn try_from(value: String) -> std::result::Result<Self, Self::Error> {
        Self::try_new(value)
    }
}

impl TryFrom<&str> for Identifier {
    type Error = result::Error;

    fn try_from(value: &str) -> std::result::Result<Self, Self::Error> {
        Self::try_new(value.to_string())
    }
}

impl From<Identifier> for String {
    fn from(value: Identifier) -> Self {
        value.0
    }
}

impl Deref for Identifier {
    type Target = String;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Debug, Error)]
#[error("Malformed identifier {0}")]
struct MalformedIdentifierErr(String);

impl Parsable for Identifier {
    type Arg = ();
    type Parsed = Identifier;

    fn parse<'a>(
        state_stream: &mut parsable::StateStream<'a>,
        _arg: Self::Arg,
    ) -> ParseResult<'a, Self::Parsed> {
        use combine::{many, parser::char};
        let parser = (char::letter().or(token('_')))
            .and(many::<String, _, _>(char::alpha_num().or(char::char('_'))))
            .map(|(c, rest)| c.to_string() + &rest);

        parser
            .map(|str| {
                str.try_into()
                    .expect("Something is wrong in our Identifier parser")
            })
            .parse_stream(state_stream)
            .into()
    }
}
