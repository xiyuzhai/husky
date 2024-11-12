use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VdFunctionPath {
    Prelude(VdPreludeFunctionPath),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VdPreludeFunctionPath {
    Sin,
    Cos,
}

impl VdPreludeFunctionPath {
    pub const SIN: Self = VdPreludeFunctionPath::Sin;
    pub const COS: Self = VdPreludeFunctionPath::Cos;
}

impl VdFunctionPath {
    pub const SIN: Self = VdFunctionPath::Prelude(VdPreludeFunctionPath::SIN);
    pub const COS: Self = VdFunctionPath::Prelude(VdPreludeFunctionPath::COS);
}
