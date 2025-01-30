use super::*;
use enum_index::*;
use lean_coword::ident::LnIdent;

#[derive(Debug, PartialEq, Eq, Clone, Copy, PartialOrd, Ord, Hash)]
pub enum LnTheoremPath {
    SquareNonnegative,
    TermDerivation(LnTermDerivationTheoremPath),
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, PartialOrd, Ord, Hash)]
pub enum LnTermDerivationTheoremPath {
    Custom(LnIdent),
}

impl LnTheoremPath {
    pub const SQUARE_NONNEGATIVE: Self = Self::SquareNonnegative;
}

impl LnTheoremPath {
    pub fn code(&self) -> &str {
        match self {
            LnTheoremPath::SquareNonnegative => "sq_nonneg",
            LnTheoremPath::TermDerivation(path) => path.code(),
        }
    }

    pub fn show(&self, db: &EternerDb) -> String {
        match self {
            Self::SquareNonnegative => "sq_nonneg".to_string(),
            Self::TermDerivation(path) => path.show(db),
        }
    }
}

impl LnTermDerivationTheoremPath {
    pub fn code(&self) -> &str {
        match self {
            LnTermDerivationTheoremPath::Custom(code) => code.data(),
        }
    }

    pub fn show(&self, db: &EternerDb) -> String {
        self.code().to_string()
    }
}
