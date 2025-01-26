use crate::hypothesis::VdMirHypothesisIdx;
use crate::*;
use visored_mir_opr::{opr::binary::VdMirBaseBinaryOpr, separator::VdMirBaseSeparator};
use visored_term::ty::VdType;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VdMirCoercionConstruction {
    Trivial,
    Obvious(VdMirHypothesisIdx),
}

#[enum_class::from_variants]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VdMirCoercion {
    BinaryOpr(VdOprCoercion<VdMirBaseBinaryOpr>),
    Separator(VdOprCoercion<VdMirBaseSeparator>),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct VdOprCoercion<Opr> {
    opr: Opr,
    source_ty: VdType,
    target_ty: VdType,
}
