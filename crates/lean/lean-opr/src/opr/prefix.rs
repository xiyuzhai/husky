use crate::precedence::{LnPrecedence, LnPrecedenceRange};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum LnPrefixOpr {
    Neg,
}

impl LnPrefixOpr {
    pub fn fmt_str(self) -> &'static str {
        match self {
            LnPrefixOpr::Neg => "-",
        }
    }

    pub fn outer_precedence(self) -> LnPrecedence {
        match self {
            LnPrefixOpr::Neg => LnPrecedence::Neg,
        }
    }

    pub fn precedence_range(self) -> LnPrecedenceRange {
        match self {
            LnPrefixOpr::Neg => LnPrecedenceRange::Greater(LnPrecedence::Neg),
        }
    }
}
