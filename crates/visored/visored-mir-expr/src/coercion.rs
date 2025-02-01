pub mod pow;
pub mod triangle;

use self::pow::VdMirPowCoercion;
use crate::hypothesis::VdMirHypothesisIdx;
use crate::*;
use triangle::VdMirCoercionTriangle;
use visored_mir_opr::{
    opr::{binary::VdMirBaseBinaryOpr, prefix::VdMirBasePrefixOpr},
    separator::VdMirBaseSeparator,
};
use visored_term::ty::VdType;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VdMirCoercionConstruction {
    Trivial,
    Obvious(VdMirHypothesisIdx),
}

#[enum_class::from_variants]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VdMirCoercion {
    Triangle(VdMirCoercionTriangle),
    PrefixOpr(VdMirPrefixOprCoercion),
    /// Examples:
    /// - `(a : T) - (b : T) = (a - b : T)` for `a`, `b` of type `S`
    /// - `(a : T) = (b : T) ↔ a = b` for `a`, `b` of type `S`
    BinaryOpr(VdMirBinaryOprCoercion),
    /// Examples:
    /// - `(a : T) + (b : T) = (a + b : T)` for `a`, `b` of type `S`
    Separator(VdMirSeparatorCoercion),
    Pow(VdMirPowCoercion),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct VdMirOprCoercion<Opr> {
    opr: Opr,
    source_ty: VdType,
    target_ty: VdType,
}

pub type VdMirPrefixOprCoercion = VdMirOprCoercion<VdMirBasePrefixOpr>;
pub type VdMirBinaryOprCoercion = VdMirOprCoercion<VdMirBaseBinaryOpr>;
pub type VdMirSeparatorCoercion = VdMirOprCoercion<VdMirBaseSeparator>;

impl<Opr> VdMirOprCoercion<Opr>
where
    Opr: Copy,
{
    // TODO: check construction
    pub fn new(opr: Opr, source_ty: VdType, target_ty: VdType) -> Self {
        Self {
            opr,
            source_ty,
            target_ty,
        }
    }
}

impl<Opr> VdMirOprCoercion<Opr>
where
    Opr: Copy,
{
    pub fn opr(self) -> Opr {
        self.opr
    }

    pub fn source_ty(self) -> VdType {
        self.source_ty
    }

    pub fn target_ty(self) -> VdType {
        self.target_ty
    }
}

impl VdMirOprCoercion<VdMirBaseSeparator> {
    pub fn new_eq(source_ty: VdType, target_ty: VdType) -> Self {
        Self::new(VdMirBaseSeparator::EQ, source_ty, target_ty)
    }

    pub fn new_comm_ring_mul(source_ty: VdType, target_ty: VdType) -> Self {
        Self::new(VdMirBaseSeparator::COMM_RING_MUL, source_ty, target_ty)
    }

    pub fn new_comm_ring_add(source_ty: VdType, target_ty: VdType) -> Self {
        Self::new(VdMirBaseSeparator::COMM_RING_ADD, source_ty, target_ty)
    }
}
