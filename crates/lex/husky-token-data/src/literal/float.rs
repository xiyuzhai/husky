use super::*;
use husky_term_prelude::literal::float::{F32Literal, F64Literal};

#[enum_class::from_variants]
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum FloatLiteralTokenData {
    Unspecified(UnspecifiedFloatLiteral),
    F32(F32Literal),
    F64(F64Literal),
}

#[salsa::interned]
pub struct UnspecifiedFloatLiteral {
    #[return_ref]
    pub text: String,
}

impl FloatLiteralTokenData {
    pub fn negative(self, db: &::salsa::Db) -> Self {
        match self {
            FloatLiteralTokenData::Unspecified(slf) => {
                let mut text = "-".to_string();
                text += slf.text(db);
                UnspecifiedFloatLiteral::new(db, text).into()
            }
            FloatLiteralTokenData::F32(slf) => {
                let mut text = "-".to_string();
                text += slf.text(db);
                F32Literal::new(db, -slf.value(db), text).into()
            }
            FloatLiteralTokenData::F64(slf) => {
                let mut text = "-".to_string();
                text += slf.text(db);
                F64Literal::new(db, -slf.value(db), text).into()
            }
        }
    }
}
