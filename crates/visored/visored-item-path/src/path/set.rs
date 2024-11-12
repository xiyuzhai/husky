use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VdSetPath {
    Prelude(VdPreludeSetPath),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VdPreludeSetPath {
    NaturalNumber,
    RationalNumber,
    Integer,
    RealNumber,
    ComplexNumber,
}

impl VdSetPath {
    pub const NATURAL_NUMBER: Self = Self::Prelude(VdPreludeSetPath::NaturalNumber);
    pub const RATIONAL_NUMBER: Self = Self::Prelude(VdPreludeSetPath::RationalNumber);
    pub const INTEGER: Self = Self::Prelude(VdPreludeSetPath::Integer);
    pub const REAL_NUMBER: Self = Self::Prelude(VdPreludeSetPath::RealNumber);
    pub const COMPLEX_NUMBER: Self = Self::Prelude(VdPreludeSetPath::ComplexNumber);
}
