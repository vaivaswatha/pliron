//! [Identifier]s are strings used to name entities in programming languages.

use std::{fmt::Display, ops::Deref};

use combine::{error::StdParseResult2, token, Parser, StreamOnce};
use thiserror::Error;

use crate::{
    common_traits::Verify,
    context::Context,
    error,
    parsable::{self, Parsable, StateStream},
    printable::{self, Printable},
    verify_err_noloc,
};

#[derive(Clone, Hash, PartialEq, Eq, Debug)]
/// An [Identifier] must satisfy the regex `[a-zA-Z_][a-zA-Z0-9_]*`.
/// Also see [module description](module@crate::identifier).
pub struct Identifier(String);

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

impl From<String> for Identifier {
    fn from(value: String) -> Self {
        Identifier(value)
    }
}

impl From<&str> for Identifier {
    fn from(value: &str) -> Self {
        Identifier(value.to_string())
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

impl Verify for Identifier {
    fn verify(&self, _ctx: &Context) -> error::Result<()> {
        let re = regex::Regex::new(r"[a-zA-Z_][a-zA-Z0-9_]*").unwrap();
        if !(re.is_match(&self.0)) {
            return verify_err_noloc!(MalformedIdentifierErr(self.0.clone()));
        }
        Ok(())
    }
}

impl Parsable for Identifier {
    type Arg = ();
    type Parsed = Identifier;

    fn parse<'a>(
        state_stream: &mut parsable::StateStream<'a>,
        _arg: Self::Arg,
    ) -> StdParseResult2<Self::Parsed, <StateStream<'a> as StreamOnce>::Error> {
        use combine::{many, parser::char};
        let parser = (char::letter().or(token('_')))
            .and(many::<String, _, _>(char::alpha_num().or(char::char('_'))))
            .map(|(c, rest)| c.to_string() + &rest);

        parser
            .map(|str| str.into())
            .parse_stream(state_stream)
            .into()
    }
}
