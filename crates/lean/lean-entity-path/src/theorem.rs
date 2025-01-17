use super::*;

#[derive(Debug, PartialEq, Eq, Clone, Copy, PartialOrd, Ord, Hash)]
pub enum LnTheoremPath {
    SquareNonnegative,
}

impl LnTheoremPath {
    pub const SQUARE_NONNEGATIVE: Self = Self::SquareNonnegative;
}

impl LnTheoremPath {
    pub fn code(&self) -> &str {
        match self {
            Self::SquareNonnegative => "sq_nonneg",
        }
    }

    pub fn show(&self, db: &EternerDb) -> String {
        match self {
            Self::SquareNonnegative => "sq_nonneg".to_string(),
        }
    }
}
