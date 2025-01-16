use super::*;
use visored_mir_opr::separator::folding::VdMirBaseFoldingSeparator;

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, PartialOrd, Ord)]
pub struct VdBaseFoldingSeparatorSignature {
    instantiation: VdInstantiation,
    separator: VdMirBaseFoldingSeparator,
    item_ty: VdType,
    expr_ty: VdType,
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
