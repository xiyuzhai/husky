pub mod literal;

use self::literal::{LnLiteral, LnLiteralData};
use lean_item_path::LnItemPath;

// TODO: ad hoc, use LnTermId
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum LnTerm {
    Literal(LnLiteral),
    ItemPath(LnItemPath),
}
impl LnTerm {
    pub fn new_item_path(path: LnItemPath) -> Self {
        LnTerm::ItemPath(path)
    }
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

impl LnTerm {
    pub fn show(&self, db: &::salsa::Db) -> String {
        match self {
            LnTerm::Literal(literal) => literal.show(db),
            LnTerm::ItemPath(item_path) => item_path.show(db),
        }
    }
}
