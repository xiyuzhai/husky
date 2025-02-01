pub mod relation;

use self::relation::*;
use super::*;
use visored_mir_opr::separator::chaining::VdMirBaseChainingSeparator;

#[enum_class::from_variants]
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, PartialOrd, Ord)]
pub enum VdBaseChainingSeparatorSignature {
    Iff {
        instantiation: VdInstantiation,
        item_ty: VdType,
        expr_ty: VdType,
    },
    Relation(VdBaseRelationSeparatorSignature),
}

impl From<VdBaseChainingSeparatorSignature> for VdSeparatorSignature {
    fn from(signature: VdBaseChainingSeparatorSignature) -> Self {
        VdSeparatorSignature::Base(signature.into())
    }
}

impl From<VdBaseChainingSeparatorSignature> for VdSignature {
    fn from(signature: VdBaseChainingSeparatorSignature) -> Self {
        VdSignature::Separator(signature.into())
    }
}

impl VdBaseChainingSeparatorSignature {
    pub fn new(
        separator: VdMirBaseChainingSeparator,
        instantiation: VdInstantiation,
        item_ty: VdType,
        expr_ty: VdType,
    ) -> Self {
        match separator {
            VdMirBaseChainingSeparator::Iff => VdBaseChainingSeparatorSignature::Iff {
                instantiation,
                item_ty,
                expr_ty,
            },
            VdMirBaseChainingSeparator::Relation(separator) => {
                VdBaseRelationSeparatorSignature::new(separator, instantiation, item_ty, expr_ty)
                    .into()
            }
        }
    }
}

impl VdBaseChainingSeparatorSignature {
    pub fn instantiation(self) -> VdInstantiation {
        match self {
            VdBaseChainingSeparatorSignature::Iff { instantiation, .. } => instantiation,
            VdBaseChainingSeparatorSignature::Relation(slf) => slf.instantiation(),
        }
    }

    pub fn separator(self) -> VdMirBaseChainingSeparator {
        match self {
            VdBaseChainingSeparatorSignature::Iff { .. } => VdMirBaseChainingSeparator::Iff,
            VdBaseChainingSeparatorSignature::Relation(slf) => slf.separator().into(),
        }
    }

    pub fn expr_ty(self) -> VdType {
        match self {
            VdBaseChainingSeparatorSignature::Iff { expr_ty, .. } => expr_ty,
            VdBaseChainingSeparatorSignature::Relation(slf) => slf.expr_ty(),
        }
    }

    pub fn left_item_ty(self) -> VdType {
        match self {
            VdBaseChainingSeparatorSignature::Iff { item_ty, .. } => item_ty,
            VdBaseChainingSeparatorSignature::Relation(slf) => slf.left_item_ty(),
        }
    }

    pub fn right_item_ty(self) -> VdType {
        match self {
            VdBaseChainingSeparatorSignature::Iff { item_ty, .. } => item_ty,
            VdBaseChainingSeparatorSignature::Relation(slf) => slf.right_item_ty(),
        }
    }
}
