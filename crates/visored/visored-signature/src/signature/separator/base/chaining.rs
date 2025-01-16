pub mod relation;

use self::relation::*;
use super::*;
use visored_mir_opr::separator::chaining::VdMirBaseChainingSeparator;

#[enum_class::from_variants]
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, PartialOrd, Ord)]
pub enum VdBaseChainingSeparatorSignature {
    Iff,
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
    pub const IN_SET: Self =
        VdBaseChainingSeparatorSignature::Relation(VdBaseRelationSeparatorSignature::IN_SET);
}

impl VdBaseChainingSeparatorSignature {
    pub fn new(
        separator: VdMirBaseChainingSeparator,
        instantiation: VdInstantiation,
        item_ty: VdType,
        expr_ty: VdType,
    ) -> Self {
        match separator {
            VdMirBaseChainingSeparator::Iff => VdBaseChainingSeparatorSignature::Iff,
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
            VdBaseChainingSeparatorSignature::Iff => todo!(),
            VdBaseChainingSeparatorSignature::Relation(slf) => slf.instantiation(),
        }
    }

    pub fn separator(self) -> VdMirBaseChainingSeparator {
        match self {
            VdBaseChainingSeparatorSignature::Iff => todo!(),
            VdBaseChainingSeparatorSignature::Relation(slf) => slf.separator().into(),
        }
    }

    pub fn expr_ty(self) -> VdType {
        match self {
            VdBaseChainingSeparatorSignature::Iff => todo!(),
            VdBaseChainingSeparatorSignature::Relation(slf) => slf.expr_ty(),
        }
    }

    pub fn item_ty(self) -> VdType {
        match self {
            VdBaseChainingSeparatorSignature::Iff => todo!(),
            VdBaseChainingSeparatorSignature::Relation(slf) => slf.item_ty(),
        }
    }
}
