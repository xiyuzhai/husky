pub mod literal;

use self::literal::{LnLiteral, LnLiteralData};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum LnTerm {
    Literal(LnLiteral),
}

#[salsa::interned]
pub struct LnTermId {
    #[return_ref]
    data: LnTermData,
}

#[enum_class::from_variants]
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum LnTermData {
    Literal(LnLiteralData),
}
