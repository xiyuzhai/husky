use super::*;
use visored_mir_opr::separator::chaining::VdMirBaseComparisonSeparator;

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, PartialOrd, Ord)]
pub struct VdBaseComparisonSeparatorSignature {
    instantiation: VdInstantiation,
    separator: VdMirBaseComparisonSeparator,
    item_ty: VdType,
    expr_ty: VdType,
}

impl From<VdBaseComparisonSeparatorSignature> for VdBaseChainingSeparatorSignature {
    fn from(signature: VdBaseComparisonSeparatorSignature) -> Self {
        VdBaseChainingSeparatorSignature::Relation(signature.into())
    }
}

impl VdBaseComparisonSeparatorSignature {
    pub fn new(
        separator: VdMirBaseComparisonSeparator,
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

impl VdBaseComparisonSeparatorSignature {
    pub fn instantiation(self) -> VdInstantiation {
        self.instantiation
    }

    pub fn separator(self) -> VdMirBaseComparisonSeparator {
        self.separator
    }

    pub fn item_ty(self) -> VdType {
        self.item_ty
    }

    pub fn expr_ty(self) -> VdType {
        self.expr_ty
    }
}
