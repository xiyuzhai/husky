use crate::precedence::{LnPrecedence, LnPrecedenceRange};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum LnPrefixOpr {
    Pos,
    Neg,
}

impl LnPrefixOpr {
    pub fn fmt_str(self) -> &'static str {
        match self {
            Self::Pos => "+",
            Self::Neg => "-",
        }
    }

    pub fn outer_precedence(self) -> LnPrecedence {
        match self {
            Self::Pos => LnPrecedence::Prefix,
            Self::Neg => LnPrecedence::Prefix,
        }
    }

    pub fn precedence_range(self) -> LnPrecedenceRange {
        match self {
            Self::Pos => LnPrecedenceRange::Greater(LnPrecedence::Prefix),
            Self::Neg => LnPrecedenceRange::Greater(LnPrecedence::Prefix),
        }
    }
}
