// TODO: change to LnPrecedence(usize)
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub enum LnPrecedence {
    Min,
    Iff = 20,
    Relation,
    AddSub,
    MulDiv,
    Pow,
    Sqrt,
    Sign,
    Application,
    Atom,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum LnPrecedenceRange {
    Any,
    Greater(LnPrecedence),
    NoLess(LnPrecedence),
}

/// # constants
impl LnPrecedenceRange {
    pub const APPLICATION_SUBEXPR: Self = LnPrecedenceRange::Greater(LnPrecedence::Application);
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
        assert!(LnPrecedence::AddSub < LnPrecedence::Application);
        assert!(LnPrecedence::AddSub < LnPrecedence::Atom);
        assert!(LnPrecedence::Application < LnPrecedence::Atom);
    }
}
