use super::*;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct VdBasePrefixOprSignature {
    pub instantiation: VdInstantiation,
    pub opd_ty: VdType,
    pub expr_ty: VdType,
}

impl VdBasePrefixOprSignature {
    pub fn new(instantiation: VdInstantiation, opd_ty: VdType, expr_ty: VdType) -> Self {
        Self {
            instantiation,
            opd_ty,
            expr_ty,
        }
    }
}

impl VdBasePrefixOprSignature {
    pub fn instantiation(self) -> VdInstantiation {
        self.instantiation
    }

    pub fn opd_ty(self) -> VdType {
        self.opd_ty
    }

    pub fn expr_ty(self) -> VdType {
        self.expr_ty
    }
}
