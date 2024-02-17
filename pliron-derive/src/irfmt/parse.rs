use winnow::{
    ascii::{self, escaped, multispace0},
    combinator::{alt, cut_err, delimited, opt, preceded, separated},
    error::{ErrorKind, StrContext},
    stream::Location,
    token::{none_of, one_of, take_while},
    Located, Parser,
};

use super::{Elem, Format};

type Str<'a> = Located<&'a str>;

type PResult<O, E = ContextError> = winnow::PResult<O, E>;

#[derive(Debug, PartialEq)]
pub(super) struct ContextError {
    max_pos: usize,
    context: Vec<StrContext>,
}

impl ContextError {
    fn new_at(pos: usize) -> Self {
        Self {
            max_pos: pos,
            context: Vec::new(),
        }
    }
}

impl<'a> winnow::error::ParserError<Str<'a>> for ContextError {
    fn from_error_kind(cx: &Str<'a>, _kind: ErrorKind) -> Self {
        Self::new_at(cx.location())
    }

    fn append(self, _input: &Str<'a>, _kind: ErrorKind) -> Self {
        self
    }

    fn or(self, other: Self) -> Self {
        // rightmost parse wins
        match self.max_pos.cmp(&other.max_pos) {
            std::cmp::Ordering::Less => other,
            std::cmp::Ordering::Greater => self,
            std::cmp::Ordering::Equal => {
                let max_pos = self.max_pos;
                let (mut context, other) = if self.context.capacity() > other.context.len() {
                    (self.context, other.context)
                } else {
                    (other.context, self.context)
                };
                context.extend(other);
                Self { max_pos, context }
            }
        }
    }
}

impl<'a> winnow::error::AddContext<Str<'a>, StrContext> for ContextError {
    fn add_context(mut self, cx: &Str<'a>, info: StrContext) -> Self {
        let pos = cx.location();
        match pos.cmp(&self.max_pos) {
            std::cmp::Ordering::Less => self,
            std::cmp::Ordering::Greater => {
                self.context.clear();
                self.context.push(info);
                self
            }
            std::cmp::Ordering::Equal => {
                self.context.push(info);
                self
            }
        }
    }
}

pub(crate) fn parse(input: &str) -> super::Result<Format> {
    let mut input = Located::new(input);
    let elems = match parse_asm_fmt(&mut input) {
        Ok(elems) => elems,
        Err(err) => {
            let msg = format!("{}", err);
            return Err(msg.into());
        }
    };
    Ok(Format { elems })
}

fn parse_asm_fmt(input: &mut Str) -> PResult<Vec<Elem>> {
    let mut elems = vec![];
    multispace0.parse_next(input)?;
    while !input.is_empty() {
        elems.push(parse_fmt_elem(input)?);
    }
    Ok(elems)
}

fn parse_fmt_elem(input: &mut Str) -> PResult<Elem> {
    let res = alt((parse_lit, parse_unnamed_var, parse_var, parse_directive)).parse_next(input);
    multispace0(input)?;
    res
}

fn parse_lit(input: &mut Str) -> PResult<Elem> {
    let loc = input.location();
    let string_contents = escaped(
        none_of(&['`', '\\']),
        '\\',
        one_of(&['\\', '`', 'n', 'r', 't']),
    );
    let s = delimited(backtick, string_contents, backtick)
        .context(StrContext::Label("<literal>"))
        .parse_next(input)?;
    Ok(Elem::new_lit_at(loc, s))
}

fn parse_var(input: &mut Str) -> PResult<Elem> {
    let loc = input.location();
    let s = preceded(
        dollar,
        take_while(1.., |c: char| c.is_alphanumeric() || c == '_' || c == '.'),
    )
    .context(StrContext::Label("<variable>"))
    .parse_next(input)?;
    Ok(Elem::new_var_at(loc, s))
}

fn parse_unnamed_var(input: &mut Str) -> PResult<Elem> {
    let loc = input.location();
    let s = preceded(dollar, ascii::digit1)
        .context(StrContext::Label("<variable>"))
        .parse_next(input)?;
    let idx = s.parse::<usize>().unwrap();
    Ok(Elem::new_unnamed_var_at(loc, idx))
}

fn parse_directive(input: &mut Str) -> PResult<Elem> {
    let loc = input.location();
    let name = take_while(1.., |c: char| c.is_alphanumeric() || c == '-' || c == '_')
        .context(StrContext::Label("<directive>"))
        .parse_next(input)?;

    if opt(paren_open).parse_next(input)?.is_none() {
        return Ok(Elem::new_directive_at(loc, name));
    }
    let args = cut_err(separated(0.., parse_fmt_elem, (comma, multispace0)))
        .context(StrContext::Label("<directive-argument-list>"))
        .parse_next(input)?;

    paren_close.parse_next(input)?;

    Ok(Elem::new_directive_with_args_at(loc, name, args))
}

fn backtick(input: &mut Str) -> PResult<char> {
    sym('`').parse_next(input)
}

fn dollar(input: &mut Str) -> PResult<char> {
    sym('$').parse_next(input)
}

fn paren_open(input: &mut Str) -> PResult<char> {
    sym('(').parse_next(input)
}

fn paren_close(input: &mut Str) -> PResult<char> {
    sym(')').parse_next(input)
}

fn comma(input: &mut Str) -> PResult<char> {
    sym(',').parse_next(input)
}

fn sym<'a>(c: char) -> impl Parser<Str<'a>, char, ContextError> {
    c.context(StrContext::Expected(c.into()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_literal() {
        let input = "`lit`";
        let expected = vec![Elem::new_lit_at(0, "lit")];
        assert_eq!(parse_asm_fmt(&mut Located::new(input)), Ok(expected));
    }

    #[test]
    fn literal_with_escaped_chars() {
        let input = r#"`hello\n \`world\``"#;
        let expected = vec![Elem::new_lit_at(0, r#"hello\n \`world\`"#)];
        assert_eq!(parse_asm_fmt(&mut Located::new(input)), Ok(expected));
    }

    #[test]
    fn simple_variable() {
        let input = "$var";
        let expected = vec![Elem::new_var_at(0, "var")];
        assert_eq!(parse_asm_fmt(&mut Located::new(input)), Ok(expected));
    }

    #[test]
    fn simple_directive() {
        let input = "directive";
        let expected = vec![Elem::new_directive_at(0, "directive")];
        assert_eq!(parse_asm_fmt(&mut Located::new(input)), Ok(expected));
    }

    #[test]
    fn directive_with_empty_args() {
        let input = "directive()";
        let expected = vec![Elem::new_directive_at(0, "directive")];
        assert_eq!(parse_asm_fmt(&mut Located::new(input)), Ok(expected));
    }

    #[test]
    fn directive_with_args() {
        let input = "directive($arg1, other-directive)";
        let expected = vec![Elem::new_directive_with_args_at(
            0,
            "directive",
            vec![
                Elem::new_var_at(10, "arg1"),
                Elem::new_directive_at(17, "other-directive"),
            ],
        )];
        assert_eq!(parse_asm_fmt(&mut Located::new(input)), Ok(expected));
    }
}
