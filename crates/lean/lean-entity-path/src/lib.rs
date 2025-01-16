pub mod menu;
pub mod namespace;
#[cfg(test)]
pub mod tests;
pub mod theorem;

use eterned::db::EternerDb;
use theorem::LnTheoremPath;

#[cfg(test)]
use crate::tests::*;

// TODO: ad hoc
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum LnItemPath {
    Unit,
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
    Prop,
    Theorem(LnTheoremPath),
}

impl From<LnTheoremPath> for LnItemPath {
    fn from(path: LnTheoremPath) -> Self {
        Self::Theorem(path)
    }
}

// TODO: maybe use menu?
impl LnItemPath {
    pub const UNIT: Self = LnItemPath::Unit;
    pub const NAT: Self = LnItemPath::Nat;
    pub const RAT: Self = LnItemPath::Rat;
    pub const INT: Self = LnItemPath::Int;
    pub const REAL: Self = LnItemPath::Real;
    pub const COMPLEX: Self = LnItemPath::Complex;
    pub const PROP: Self = LnItemPath::Prop;
    pub const RING_ADD: Self = LnItemPath::RingAdd;
    pub const RING_MUL: Self = LnItemPath::RingMul;
    pub const RING_POS: Self = LnItemPath::RingPos;
    pub const RING_NEG: Self = LnItemPath::RingNeg;
    pub const FIELD_DIV: Self = LnItemPath::FieldDiv;
    pub const LE: Self = LnItemPath::Le;
    pub const GE: Self = LnItemPath::Ge;
    pub const EQ: Self = LnItemPath::Eq;
    pub const REAL_SQRT: Self = LnItemPath::RealSqrt;
}

impl LnItemPath {
    pub fn show(&self, db: &EternerDb) -> String {
        match self {
            LnItemPath::Unit => "()".to_string(),
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
            LnItemPath::Prop => "Prop".to_string(),
            LnItemPath::Theorem(ln_theorem_path) => todo!(),
        }
    }
}
