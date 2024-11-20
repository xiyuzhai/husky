use super::*;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct VdBaseSqrtSignature {
    instantiation: VdInstantiation,
    base_ty: VdType,
    expr_ty: VdType,
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
