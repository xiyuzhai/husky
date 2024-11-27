use super::*;

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct VdBaseSeparatorSignature {
    instantiation: VdInstantiation,
    item_ty: VdType,
    expr_ty: VdType,
}

impl From<VdBaseSeparatorSignature> for VdSignature {
    fn from(signature: VdBaseSeparatorSignature) -> Self {
        VdSignature::Separator(signature.into())
    }
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
