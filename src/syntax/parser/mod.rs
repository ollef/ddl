use lalrpop_util;

use std::fmt;
use std::rc::Rc;
use std::str::FromStr;

use syntax::ast::{binary, host, Program};
use source::BytePos;

mod lexer;
mod grammar;

#[cfg(test)]
mod tests;

use self::lexer::Lexer;

pub type ParseError = lalrpop_util::ParseError<BytePos, String, GrammarError>;

#[derive(Debug, Fail, Clone, Eq, PartialEq)]
pub enum GrammarError {
    #[fail(display = "{}", _0)] Lexer(lexer::Error),
    #[fail(display = "{}", _0)] IntSuffix(host::ParseIntSuffixError),
    #[fail(display = "{}", _0)] HostTypeConst(host::ParseTypeConstError),
}

impl From<lexer::Error> for GrammarError {
    fn from(src: lexer::Error) -> GrammarError {
        GrammarError::Lexer(src)
    }
}

impl From<host::ParseIntSuffixError> for GrammarError {
    fn from(src: host::ParseIntSuffixError) -> GrammarError {
        GrammarError::IntSuffix(src)
    }
}

impl From<host::ParseTypeConstError> for GrammarError {
    fn from(src: host::ParseTypeConstError) -> GrammarError {
        GrammarError::HostTypeConst(src)
    }
}

fn from_lalrpop_err<L, T: fmt::Debug, E>(
    src: lalrpop_util::ParseError<L, T, E>,
) -> lalrpop_util::ParseError<L, String, E> {
    use lalrpop_util::ParseError::*;

    match src {
        InvalidToken { location } => InvalidToken { location },
        UnrecognizedToken { token, expected } => UnrecognizedToken {
            token: token.map(|(lo, token, hi)| (lo, format!("{:?}", token), hi)),
            expected,
        },
        ExtraToken {
            token: (lo, token, hi),
        } => ExtraToken {
            token: (lo, format!("{:?}", token), hi),
        },
        User { error } => User { error },
    }
}

impl FromStr for Program<String> {
    type Err = ParseError;

    fn from_str(src: &str) -> Result<Program<String>, ParseError> {
        grammar::parse_Program(Lexer::new(src).map(|x| x.map_err(GrammarError::from)))
            .map_err(from_lalrpop_err)
    }
}

impl FromStr for host::Expr<String> {
    type Err = ParseError;

    fn from_str(src: &str) -> Result<host::Expr<String>, ParseError> {
        grammar::parse_HostExpr(Lexer::new(src).map(|x| x.map_err(GrammarError::from)))
            .map(|expr| Rc::try_unwrap(expr).unwrap())
            .map_err(from_lalrpop_err)
    }
}

impl FromStr for host::Type<String> {
    type Err = ParseError;

    fn from_str(src: &str) -> Result<host::Type<String>, ParseError> {
        grammar::parse_HostType(Lexer::new(src).map(|x| x.map_err(GrammarError::from)))
            .map(|ty| Rc::try_unwrap(ty).unwrap())
            .map_err(from_lalrpop_err)
    }
}

impl FromStr for binary::Type<String> {
    type Err = ParseError;

    fn from_str(src: &str) -> Result<binary::Type<String>, ParseError> {
        grammar::parse_BinaryType(Lexer::new(src).map(|x| x.map_err(GrammarError::from)))
            .map(|ty| Rc::try_unwrap(ty).unwrap())
            .map_err(from_lalrpop_err)
    }
}
