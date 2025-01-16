use super::*;
use visored_mir_opr::separator::chaining::VdMirBaseContainmentSeparator;

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, PartialOrd, Ord)]
pub enum VdBaseContainmentSeparatorSignature {
    InSet {
        instantiation: VdInstantiation,
        element_ty: VdType,
        set_ty: VdType,
        expr_ty: VdType,
    },
}

impl From<VdBaseContainmentSeparatorSignature> for VdBaseChainingSeparatorSignature {
    fn from(signature: VdBaseContainmentSeparatorSignature) -> Self {
        VdBaseChainingSeparatorSignature::Relation(signature.into())
    }
}

impl From<VdBaseContainmentSeparatorSignature> for VdBaseSeparatorSignature {
    fn from(signature: VdBaseContainmentSeparatorSignature) -> Self {
        VdBaseSeparatorSignature::Chaining(signature.into())
    }
}

impl From<VdBaseContainmentSeparatorSignature> for VdSignature {
    fn from(signature: VdBaseContainmentSeparatorSignature) -> Self {
        VdSignature::Separator(VdSeparatorSignature::Base(signature.into()))
    }
}

impl VdBaseContainmentSeparatorSignature {
    pub fn new(
        separator: VdMirBaseContainmentSeparator,
        instantiation: VdInstantiation,
        item_ty: VdType,
        expr_ty: VdType,
    ) -> Self {
        match separator {
            VdMirBaseContainmentSeparator::InSet => todo!(),
            VdMirBaseContainmentSeparator::Notin => todo!(),
            VdMirBaseContainmentSeparator::Subset => todo!(),
            VdMirBaseContainmentSeparator::Supset => todo!(),
            VdMirBaseContainmentSeparator::Subseteq => todo!(),
            VdMirBaseContainmentSeparator::Supseteq => todo!(),
            VdMirBaseContainmentSeparator::Subseteqq => todo!(),
            VdMirBaseContainmentSeparator::Supseteqq => todo!(),
            VdMirBaseContainmentSeparator::Subsetneq => todo!(),
            VdMirBaseContainmentSeparator::Supsetneq => todo!(),
        }
    }

    pub fn new_in_set(
        instantiation: VdInstantiation,
        element_ty: VdType,
        set_ty: VdType,
        expr_ty: VdType,
    ) -> Self {
        VdBaseContainmentSeparatorSignature::InSet {
            instantiation,
            element_ty,
            set_ty,
            expr_ty,
        }
    }
}

impl VdBaseContainmentSeparatorSignature {
    pub fn instantiation(self) -> VdInstantiation {
        match self {
            VdBaseContainmentSeparatorSignature::InSet { instantiation, .. } => instantiation,
        }
    }

    pub fn left_item_ty(self) -> VdType {
        match self {
            VdBaseContainmentSeparatorSignature::InSet { element_ty, .. } => element_ty,
        }
    }

    pub fn right_item_ty(self) -> VdType {
        match self {
            VdBaseContainmentSeparatorSignature::InSet { set_ty, .. } => set_ty,
        }
    }

    pub fn expr_ty(self) -> VdType {
        match self {
            VdBaseContainmentSeparatorSignature::InSet { expr_ty, .. } => expr_ty,
        }
    }

    pub fn separator(self) -> VdMirBaseContainmentSeparator {
        match self {
            VdBaseContainmentSeparatorSignature::InSet { .. } => {
                VdMirBaseContainmentSeparator::IN_SET
            }
        }
    }
}
