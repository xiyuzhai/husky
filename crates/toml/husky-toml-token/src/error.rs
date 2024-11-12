use husky_text_protocol::offset::TextOffset;
use thiserror::Error;

#[derive(Debug, Error, PartialEq, Eq, Clone, Hash)]
pub enum TomlTokenError {
    #[error("invalid char in string {0} {1}")]
    InvalidCharInString(TextOffset, char),
    #[error("todo")]
    InvalidEscape(TextOffset, char),
    #[error("todo")]
    InvalidHexEscape(TextOffset, char),
    #[error("todo")]
    InvalidEscapeValue(TextOffset, u32),
    #[error("todo")]
    NewlineInString(TextOffset),
    #[error("todo")]
    UnexpectedChar(char),
    #[error("todo")]
    UnterminatedString,
    #[error("todo")]
    NewlineInTableKey(TextOffset),
    #[error("todo")]
    MultilineStringKey(TextOffset),
    #[error("todo")]
    Wanted {
        at: usize,
        expected: &'static str,
        found: &'static str,
    },
}

pub type TomlTokenResult<T> = Result<T, TomlTokenError>;
