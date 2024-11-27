use super::*;

#[salsa::derive_debug_with_db]
#[enum_class::from_variants]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdSqrtSignature {
    Base(VdBaseSqrtSignature),
}

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct VdBaseSqrtSignature {
    instantiation: VdInstantiation,
    base_ty: VdType,
    expr_ty: VdType,
}

impl From<VdBaseSqrtSignature> for VdSignature {
    fn from(value: VdBaseSqrtSignature) -> Self {
        VdSignature::Sqrt(VdSqrtSignature::Base(value))
    }
}

impl VdBaseSqrtSignature {
    pub fn new(instantiation: VdInstantiation, base_ty: VdType, expr_ty: VdType) -> Self {
        Self {
            instantiation,
            base_ty,
            expr_ty,
        }
    }
}

impl VdBaseSqrtSignature {
    pub fn instantiation(self) -> VdInstantiation {
        self.instantiation
    }

    pub fn base_ty(self) -> VdType {
        self.base_ty
    }

    pub fn expr_ty(self) -> VdType {
        self.expr_ty
    }
}
