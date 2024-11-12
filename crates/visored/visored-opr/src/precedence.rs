#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
pub struct VdPrecedence(u64);

impl VdPrecedence {
    pub fn raw(&self) -> u64 {
        self.0
    }
}

impl std::fmt::Debug for VdPrecedence {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            Self::MIN => write!(f, "VdPrecedence::MIN"),
            Self::SEMICOLON => write!(f, "VdPrecedence::SEMICOLON"),
            Self::COMMA => write!(f, "VdPrecedence::COMMA"),
            Self::RELATION => write!(f, "VdPrecedence::EQ"),
            Self::ADD_SUB => write!(f, "VdPrecedence::ADD"),
            Self::MUL_DIV => write!(f, "VdPrecedence::MUL"),
            Self::SPACE => write!(f, "VdPrecedence::SPACE"),
            Self::ATOM => write!(f, "VdPrecedence::ATOM"),
            Self::MAX => write!(f, "VdPrecedence::MAX"),
            _ => write!(f, "VdPrecedence({})", self.raw()),
        }
    }
}

impl std::fmt::Display for VdPrecedence {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            Self::MIN => write!(f, "VdPrecedence::MIN"),
            Self::SEMICOLON => write!(f, "VdPrecedence::SEMICOLON"),
            Self::COMMA => write!(f, "VdPrecedence::COMMA"),
            Self::RELATION => write!(f, "VdPrecedence::EQ"),
            Self::ADD_SUB => write!(f, "VdPrecedence::ADD"),
            Self::MUL_DIV => write!(f, "VdPrecedence::MUL"),
            Self::SPACE => write!(f, "VdPrecedence::SPACE"),
            Self::ATOM => write!(f, "VdPrecedence::ATOM"),
            Self::MAX => write!(f, "VdPrecedence::MAX"),
            _ => write!(f, "VdPrecedence({})", self.raw()),
        }
    }
}

impl VdPrecedence {
    pub const MIN: Self = VdPrecedence(0);
    pub const INCOMPLTE_DELIMITED: Self = VdPrecedence(10);
    pub const RELATION: Self = VdPrecedence(500);
    pub const SEMICOLON: Self = VdPrecedence(1000);
    pub const COMMA: Self = VdPrecedence(5000);
    pub const ADD_SUB: Self = VdPrecedence(20000);
    pub const REDUCE_PREFIX: Self = VdPrecedence(25000);
    pub const DIFFERENTIAL: Self = VdPrecedence(25000);
    pub const MUL_DIV: Self = VdPrecedence(30000);
    pub const SPACE: Self = VdPrecedence(100000);
    pub const ATOM: Self = VdPrecedence(u64::MAX - 1);
    pub const MAX: Self = VdPrecedence(u64::MAX);
}

#[test]
fn vd_precedence_works() {
    // (a; b
    assert!(VdPrecedence::INCOMPLTE_DELIMITED < VdPrecedence::SEMICOLON);
    // a, b < 1
    assert!(VdPrecedence::RELATION < VdPrecedence::COMMA);
    // \sum a+ b
    assert!(VdPrecedence::ADD_SUB < VdPrecedence::REDUCE_PREFIX);
    // \sum a b
    assert!(VdPrecedence::REDUCE_PREFIX < VdPrecedence::MUL_DIV);
    // a+a\times b
    assert!(VdPrecedence::ADD_SUB < VdPrecedence::MUL_DIV);
    // a\times b c
    assert!(VdPrecedence::MUL_DIV < VdPrecedence::SPACE);
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdPrecedenceRange {
    Any,
    Greater(VdPrecedence),
    NoLess(VdPrecedence),
}

/// # constants
impl VdPrecedenceRange {
    pub const RIGHT_DELIMITER_LEFT: Self =
        VdPrecedenceRange::Greater(VdPrecedence::INCOMPLTE_DELIMITED);
    pub const SPACE_LEFT: Self = VdPrecedenceRange::NoLess(VdPrecedence::SPACE);
    pub const ADD_SUB_LEFT: Self = VdPrecedenceRange::NoLess(VdPrecedence::ADD_SUB);
    pub const MUL_DIV_LEFT: Self = VdPrecedenceRange::NoLess(VdPrecedence::MUL_DIV);
    pub const COMPARISON_LEFT: Self = VdPrecedenceRange::NoLess(VdPrecedence::RELATION);
}

/// # methods
impl VdPrecedenceRange {
    pub fn contains(self, precedence: VdPrecedence) -> bool {
        match self {
            VdPrecedenceRange::Any => true,
            VdPrecedenceRange::Greater(p) => precedence > p,
            VdPrecedenceRange::NoLess(p) => precedence >= p,
        }
    }
}

#[test]
fn vd_precedence_range_works() {
    assert!(VdPrecedenceRange::SPACE_LEFT.contains(VdPrecedence::SPACE));
    assert!(!VdPrecedenceRange::SPACE_LEFT.contains(VdPrecedence::ADD_SUB));
}
