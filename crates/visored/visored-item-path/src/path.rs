pub mod function;
pub mod set;

use self::{function::*, set::*};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VdItemPath {
    Set(VdSetPath),
    Function(VdFunctionPath),
}

impl VdItemPath {
    // # sets
    pub const NATURAL_NUMBER: Self = VdItemPath::Set(VdSetPath::NATURAL_NUMBER);
    pub const RATIONAL_NUMBER: Self = VdItemPath::Set(VdSetPath::RATIONAL_NUMBER);
    pub const INTEGER: Self = VdItemPath::Set(VdSetPath::INTEGER);
    pub const REAL_NUMBER: Self = VdItemPath::Set(VdSetPath::REAL_NUMBER);
    pub const COMPLEX_NUMBER: Self = VdItemPath::Set(VdSetPath::COMPLEX_NUMBER);
    // # functions
    pub const SIN: Self = VdItemPath::Function(VdFunctionPath::SIN);
    pub const COS: Self = VdItemPath::Function(VdFunctionPath::COS);
}
