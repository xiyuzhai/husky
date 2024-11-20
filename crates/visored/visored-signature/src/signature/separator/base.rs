use super::*;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct VdBaseSeparatorSignature {
    instantiation: VdInstantiation,
    item_ty: VdType,
    expr_ty: VdType,
}

impl VdBaseSeparatorSignature {
    pub fn new(instantiation: VdInstantiation, item_ty: VdType, expr_ty: VdType) -> Self {
        Self {
            instantiation,
            item_ty,
            expr_ty,
        }
    }
}

impl VdBaseSeparatorSignature {
    pub fn instantiation(self) -> VdInstantiation {
        self.instantiation
    }

    pub fn item_ty(self) -> VdType {
        self.item_ty
    }

    pub fn expr_ty(self) -> VdType {
        self.expr_ty
    }
}
