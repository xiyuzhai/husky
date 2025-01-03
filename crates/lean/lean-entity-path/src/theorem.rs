#[derive(Debug, PartialEq, Eq, Clone, Copy)]
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
}
