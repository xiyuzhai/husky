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
    pub const IFF: Self = LnPrecedence::Iff;
    pub const POW: Self = LnPrecedence::Pow;
    pub const NEG: Self = LnPrecedence::Neg;
    pub const ARG: Self = LnPrecedence::Arg;
    pub const ATOM: Self = LnPrecedence::Max;
}

impl LnPrecedenceRange {
    pub const APPLICATION_SUBEXPR: Self = LnPrecedenceRange::Greater(LnPrecedence::ARG);
    pub const IFF_LEFT: Self = LnPrecedenceRange::Greater(LnPrecedence::IFF);
    pub const IFF_RIGHT: Self = LnPrecedenceRange::NoLess(LnPrecedence::IFF);
    /// `^` is infixr in lean4, see `src/lean/Init/Notation.lean` in lean4 repo
    pub const POW_BASE: Self = LnPrecedenceRange::Greater(LnPrecedence::POW);
    pub const POW_EXPONENT: Self = LnPrecedenceRange::NoLess(LnPrecedence::POW);
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
        assert!(LnPrecedence::AddSub < LnPrecedence::ARG);
        assert!(LnPrecedence::AddSub < LnPrecedence::ATOM);
        assert!(LnPrecedence::ARG < LnPrecedence::ATOM);
    }
}
