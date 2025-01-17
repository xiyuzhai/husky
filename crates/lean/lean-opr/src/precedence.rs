/// see `src/lean/Init/Notation.lean` in lean4 repo
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub enum LnPrecedence {
    Min,
    Iff = 20,
    Relation,
    AddSub,
    MulDiv,
    Neg = 75,
    Pow = 80,
    Arg = 1023,
    Max = 1024,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum LnPrecedenceRange {
    Any,
    Greater(LnPrecedence),
    NoLess(LnPrecedence),
}

/// # constants
impl LnPrecedence {
    pub const APPLICATION: Self = LnPrecedence::Arg;
    pub const ATOM: Self = LnPrecedence::Max;
}

impl LnPrecedenceRange {
    pub const APPLICATION_SUBEXPR: Self = LnPrecedenceRange::Greater(LnPrecedence::Arg);
    pub const IFF_LEFT: Self = LnPrecedenceRange::Greater(LnPrecedence::Iff);
    pub const IFF_RIGHT: Self = LnPrecedenceRange::NoLess(LnPrecedence::Iff);
}

/// # methods
impl LnPrecedenceRange {
    pub fn include(self, precedence: LnPrecedence) -> bool {
        match self {
            LnPrecedenceRange::Any => true,
            LnPrecedenceRange::Greater(p) => precedence > p,
            LnPrecedenceRange::NoLess(p) => precedence >= p,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_precedence_ordering() {
        assert!(LnPrecedence::AddSub < LnPrecedence::APPLICATION);
        assert!(LnPrecedence::AddSub < LnPrecedence::ATOM);
        assert!(LnPrecedence::APPLICATION < LnPrecedence::ATOM);
    }
}
