use super::*;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdAttachSignature {
    Power(VdPowerSignature),
}
impl VdAttachSignature {
    pub fn expr_ty(self) -> VdType {
        match self {
            VdAttachSignature::Power(signature) => signature.expr_ty(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct VdPowerSignature {
    instantiation: VdInstantiation,
    base_ty: VdType,
    exponent_ty: VdType,
    expr_ty: VdType,
}

impl VdPowerSignature {
    pub fn new(
        instantiation: VdInstantiation,
        base_ty: VdType,
        exponent_ty: VdType,
        expr_ty: VdType,
    ) -> Self {
        Self {
            instantiation,
            base_ty,
            exponent_ty,
            expr_ty,
        }
    }
}

impl VdPowerSignature {
    pub fn instantiation(self) -> VdInstantiation {
        self.instantiation
    }

    pub fn base_ty(self) -> VdType {
        self.base_ty
    }

    pub fn exponent_ty(self) -> VdType {
        self.exponent_ty
    }

    pub fn expr_ty(self) -> VdType {
        self.expr_ty
    }
}
