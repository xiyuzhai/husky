use super::*;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct VdBaseFracSignature {
    instantiation: VdInstantiation,
    numerator_ty: VdType,
    denominator_ty: VdType,
    expr_ty: VdType,
}

impl VdBaseFracSignature {
    pub fn new(
        instantiation: VdInstantiation,
        numerator_ty: VdType,
        denominator_ty: VdType,
        expr_ty: VdType,
    ) -> Self {
        Self {
            instantiation,
            numerator_ty,
            denominator_ty,
            expr_ty,
        }
    }
}

impl VdBaseFracSignature {
    pub fn instantiation(self) -> VdInstantiation {
        self.instantiation
    }

    pub fn numerator_ty(self) -> VdType {
        self.numerator_ty
    }

    pub fn denominator_ty(self) -> VdType {
        self.denominator_ty
    }

    pub fn expr_ty(self) -> VdType {
        self.expr_ty
    }
}
