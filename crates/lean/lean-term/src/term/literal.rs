use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LnLiteral(LnTermId);

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum LnLiteralData {
    Nat(String),
}

impl LnLiteral {
    pub fn new(data: LnLiteralData, db: &::salsa::Db) -> Self {
        Self(LnTermId::new(db, data.into()))
    }
}

impl LnLiteral {
    pub fn data(self, db: &::salsa::Db) -> &LnLiteralData {
        match self.0.data(db) {
            LnTermData::Literal(data) => data,
            _ => unreachable!(),
        }
    }
}

impl LnLiteralData {
    pub fn str(&self) -> &str {
        match self {
            LnLiteralData::Nat(s) => s,
        }
    }
}

impl AsRef<str> for LnLiteralData {
    fn as_ref(&self) -> &str {
        self.str()
    }
}

impl std::fmt::Display for LnLiteralData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.str())
    }
}
