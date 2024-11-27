mod convexity;
pub mod delimiter;
mod error;
pub mod jar;
mod keyword;
mod literal;
mod punctuation;
mod wordopr;

pub use self::convexity::*;
pub use self::error::*;
pub use self::keyword::*;
pub use self::literal::*;
pub use self::punctuation::*;
pub use self::wordopr::*;

use self::jar::{TokenDataJar as Jar, *};
use husky_coword::*;

#[cfg(feature = "protocol_support")]
use husky_token_protocol::TokenClass;

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[enum_class::from_variants]
pub enum TokenData {
    Keyword(Keyword),
    Ident(Ident),
    Label(Label),
    Punctuation(Punctuation),
    WordOpr(WordOpr),
    Literal(LiteralTokenData),
    Error(TokenDataError),
}

/// # constants
impl TokenData {
    pub const VERTICAL: Self = TokenData::Punctuation(Punctuation::VERT);
    pub const EQ: Self = TokenData::Punctuation(Punctuation::EQ);
    pub const INLINE_LCURL: Self = TokenData::Punctuation(Punctuation::INLINE_LCURL);
    pub const INLINE_RCURL: Self = TokenData::Punctuation(Punctuation::INLINE_RCURL);
    pub const NESTED_LCURL: Self = TokenData::Punctuation(Punctuation::NESTED_LCURL);
    pub const NESTED_RCURL: Self = TokenData::Punctuation(Punctuation::NESTED_RCURL);
}

#[cfg(feature = "protocol_support")]
impl TokenData {
    // overridable given more information
    pub fn default_token_class(self) -> TokenClass {
        match self {
            TokenData::Keyword(kw) => kw.class().into(),
            TokenData::Punctuation(_) => TokenClass::Punctuation,
            TokenData::WordOpr(_) => TokenClass::WordOpr,
            TokenData::Literal(_) => TokenClass::Literal,
            TokenData::Ident(_) => TokenClass::Ident,
            TokenData::Label(_) => TokenClass::Label,
            TokenData::Error(_) => TokenClass::Error,
        }
    }
}

impl std::hash::Hash for TokenData {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        core::mem::discriminant(self).hash(state);
    }
}
