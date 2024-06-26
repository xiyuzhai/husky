use crate::*;

use thiserror::Error;

#[derive(Debug, Error, PartialEq, Eq, Clone, Copy)]
#[salsa::derive_debug_with_db]
pub enum TokenDataError {
    #[error("incomplete string literal before end of file")]
    IncompleteStringLiteralBeforeEof,
    #[error("incomplete string literal before end of line")]
    IncompleteStringLiteralBeforeEol,
    #[error("unexpected char after backslash")]
    UnexpectedCharAfterBackslash(char),
    #[error("unrecognized char")]
    UnrecognizedChar(char),
    #[error("ill-formed literal")]
    IllFormedLiteral(LiteralTokenData),
    #[error("number pseudoliteral")]
    NumberPseudoLiteral(NumberPseudoLiteral),
    #[error("parse int error")]
    ParseIntError,
    #[error("invalid integer suffix")]
    InvalidIntegerSuffix,
    #[error("invalid float suffix")]
    InvalidFloatSuffix,
    #[error("invalid identifier")]
    InvalidIdent,
    #[error("nothing after `'`")]
    NothingAfterSingleQuote,
    #[error("new line after `'`")]
    NewLineAfterSingleQuote,
    #[error("InvalidLabel")]
    InvalidLabel,
    #[error("NoNegativeForLiteral")]
    NoNegativeForLiteral(LiteralTokenData),
    #[error("`}}` missing `{{`")]
    RcurlMissingMatchingLcurl,
    #[error("expected keyword after `assoc`")]
    ExpectedKeywordAfterAssoc,
}

#[derive(Debug, Error, PartialEq, Eq, Clone, Copy)]
pub enum NumberPseudoLiteral {}

pub type TokenDataResult<T> = Result<T, TokenDataError>;
