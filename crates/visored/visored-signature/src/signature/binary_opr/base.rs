use super::*;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct VdBaseBinaryOprSignature {
    pub instantiation: VdInstantiation,
    pub lopd_ty: VdType,
    pub ropd_ty: VdType,
    pub expr_ty: VdType,
}

impl VdBaseBinaryOprSignature {
    pub fn new(
        instantiation: VdInstantiation,
        lopd_ty: VdType,
        ropd_ty: VdType,
        expr_ty: VdType,
    ) -> Self {
        Self {
            instantiation,
            lopd_ty,
            ropd_ty,
            expr_ty,
        }
    }
}

impl VdBaseBinaryOprSignature {
    pub fn instantiation(self) -> VdInstantiation {
        self.instantiation
    }

    pub fn lopd_ty(self) -> VdType {
        self.lopd_ty
    }

    pub fn ropd_ty(self) -> VdType {
        self.ropd_ty
    }

    pub fn expr_ty(self) -> VdType {
        self.expr_ty
    }
}
