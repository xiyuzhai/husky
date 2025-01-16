use super::*;
use visored_mir_opr::separator::folding::VdMirBaseFoldingSeparator;

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, PartialOrd, Ord)]
pub struct VdBaseFoldingSeparatorSignature {
    instantiation: VdInstantiation,
    separator: VdMirBaseFoldingSeparator,
    item_ty: VdType,
    expr_ty: VdType,
}

impl From<VdBaseFoldingSeparatorSignature> for VdSeparatorSignature {
    fn from(signature: VdBaseFoldingSeparatorSignature) -> Self {
        VdSeparatorSignature::Base(signature.into())
    }
}

impl From<VdBaseFoldingSeparatorSignature> for VdSignature {
    fn from(signature: VdBaseFoldingSeparatorSignature) -> Self {
        VdSignature::Separator(signature.into())
    }
}

impl VdBaseFoldingSeparatorSignature {
    pub fn new(
        separator: VdMirBaseFoldingSeparator,
        instantiation: VdInstantiation,
        item_ty: VdType,
        expr_ty: VdType,
    ) -> Self {
        Self {
            instantiation,
            separator,
            item_ty,
            expr_ty,
        }
    }
}

impl VdBaseFoldingSeparatorSignature {
    pub fn instantiation(&self) -> VdInstantiation {
        self.instantiation
    }

    pub fn separator(&self) -> VdMirBaseFoldingSeparator {
        self.separator
    }

    pub fn item_ty(&self) -> VdType {
        self.item_ty
    }

    pub fn expr_ty(&self) -> VdType {
        self.expr_ty
    }
}
