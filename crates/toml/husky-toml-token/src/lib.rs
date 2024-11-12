#![feature(const_trait_impl)]
#![feature(try_trait_v2)]
mod error;
pub mod jar;
mod line_group;
mod sheet;
mod special;
mod stream;
#[cfg(test)]
mod tests;
mod tokenize;

pub use self::error::*;
pub use self::sheet::*;
pub use self::special::*;
pub use self::stream::*;

use self::jar::TomlTokenJar as Jar;
use crate::jar::TomlTokenDb;
use husky_coword::Coword;
use husky_text_protocol::{offset::TextOffsetRange, range::TextRange};
use std::char;
use std::str;
use std::sync::Arc;
use tokenize::*;

pub type StringValue = Arc<str>;

/// tokens in toml file
#[derive(Debug, PartialEq, Eq)]
pub struct TomlToken {
    offset_range: TextOffsetRange,
    range: TextRange,
    data: TomlTokenData,
}

impl TomlToken {
    pub fn new(span: TextOffsetRange, range: TextRange, data: TomlTokenData) -> Self {
        Self {
            offset_range: span,
            range,
            data,
        }
    }

    pub fn offset_range(&self) -> TextOffsetRange {
        self.offset_range
    }

    pub fn range(&self) -> TextRange {
        self.range
    }

    pub fn data(&self) -> &TomlTokenData {
        &self.data
    }
}

/// variants for tokens in toml file
#[derive(Debug, Eq, PartialEq, Clone)]
pub enum TomlTokenData {
    Comment,
    Special(TomlSpecialToken),
    Word(Coword),
    StringLiteral { val: StringValue, multiline: bool },
    Err(TomlTokenError),
}

impl TomlTokenData {
    pub fn describe(&self) -> &'static str {
        match *self {
            TomlTokenData::Word(_) => "a word",
            TomlTokenData::Comment => "a comment",
            TomlTokenData::Special(special) => special.describe(),
            TomlTokenData::StringLiteral { multiline, .. } => {
                if multiline {
                    "a multiline string"
                } else {
                    "a string"
                }
            }
            TomlTokenData::Err(_) => todo!(),
        }
    }
}

impl std::ops::FromResidual<Result<core::convert::Infallible, TomlTokenError>> for TomlTokenData {
    fn from_residual(residual: Result<core::convert::Infallible, TomlTokenError>) -> Self {
        match residual {
            Ok(_) => unreachable!(),
            Err(e) => TomlTokenData::Err(e),
        }
    }
}
