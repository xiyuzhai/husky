pub mod jar;
pub mod menu;
pub mod namespace;
#[cfg(test)]
pub mod tests;

use self::jar::LnItemPathJar as Jar;
#[cfg(test)]
use crate::tests::*;

// TODO: ad hoc
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum LnItemPath {
    Nat,
    Rat,
    Int,
    Real,
    Complex,
    RingAdd,
    RingMul,
    RingPos,
    RingNeg,
    FieldDiv,
    Le,
    Ge,
    Eq,
    RealSqrt,
}

// TODO: maybe use menu?
impl LnItemPath {
    pub const NAT: Self = Self::Nat;
    pub const RAT: Self = Self::Rat;
    pub const INT: Self = Self::Int;
    pub const REAL: Self = Self::Real;
    pub const COMPLEX: Self = Self::Complex;
    pub const RING_ADD: Self = Self::RingAdd;
    pub const RING_MUL: Self = Self::RingMul;
    pub const RING_POS: Self = Self::RingPos;
    pub const RING_NEG: Self = Self::RingNeg;
    pub const FIELD_DIV: Self = Self::FieldDiv;
    pub const LE: Self = Self::Le;
    pub const GE: Self = Self::Ge;
    pub const EQ: Self = Self::Eq;
    pub const REAL_SQRT: Self = Self::RealSqrt;
}

impl LnItemPath {
    pub fn show(&self, db: &::salsa::Db) -> String {
        match self {
            LnItemPath::Nat => "ℕ".to_string(),
            LnItemPath::Rat => "ℚ".to_string(),
            LnItemPath::Int => "ℤ".to_string(),
            LnItemPath::Real => "ℝ".to_string(),
            LnItemPath::Complex => "ℂ".to_string(),
            LnItemPath::RingAdd => "+".to_string(),
            LnItemPath::RingMul => "*".to_string(),
            LnItemPath::RingPos => "+".to_string(),
            LnItemPath::RingNeg => "-".to_string(),
            LnItemPath::FieldDiv => "/".to_string(),
            LnItemPath::Le => "≤".to_string(),
            LnItemPath::Ge => "≥".to_string(),
            LnItemPath::Eq => "=".to_string(),
            LnItemPath::RealSqrt => "√".to_string(),
        }
    }
}
