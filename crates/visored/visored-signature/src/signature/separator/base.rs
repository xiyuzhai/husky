pub mod chaining;
pub mod folding;

use self::{chaining::*, folding::*};
use super::*;
use visored_entity_path::path::{trai_item::VdTraitItemPath, VdItemPath};
use visored_mir_opr::separator::VdMirBaseSeparator;

#[enum_class::from_variants]
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, PartialOrd, Ord)]
pub enum VdBaseSeparatorSignature {
    Chaining(VdBaseChainingSeparatorSignature),
    Folding(VdBaseFoldingSeparatorSignature),
}

impl From<VdBaseSeparatorSignature> for VdSignature {
    fn from(signature: VdBaseSeparatorSignature) -> Self {
        VdSignature::Separator(signature.into())
    }
}

impl VdBaseSeparatorSignature {
    pub fn new(instantiation: VdInstantiation, item_ty: VdType, expr_ty: VdType) -> Self {
        let VdItemPath::TraitItem(path) = instantiation.path() else {
            unreachable!()
        };
        let separator = match path {
            VdTraitItemPath::Iff => VdMirBaseSeparator::IFF,
            VdTraitItemPath::InSet => todo!(),
            VdTraitItemPath::GroupMul => todo!(),
            VdTraitItemPath::AbelianGroupAdd => todo!(),
            VdTraitItemPath::NatAdd => VdMirBaseSeparator::COMM_RING_ADD,
            VdTraitItemPath::NatMul => VdMirBaseSeparator::COMM_RING_MUL,
            VdTraitItemPath::CommRingAdd => VdMirBaseSeparator::COMM_RING_ADD,
            VdTraitItemPath::CommRingSub => todo!(),
            VdTraitItemPath::CommRingMul => VdMirBaseSeparator::COMM_RING_MUL,
            VdTraitItemPath::CommRingPower => todo!(),
            VdTraitItemPath::CommRingPos => todo!(),
            VdTraitItemPath::CommRingNeg => todo!(),
            VdTraitItemPath::Eq => VdMirBaseSeparator::EQ,
            VdTraitItemPath::Ne => VdMirBaseSeparator::NE,
            VdTraitItemPath::Lt => VdMirBaseSeparator::LT,
            VdTraitItemPath::Gt => VdMirBaseSeparator::GT,
            VdTraitItemPath::Le => VdMirBaseSeparator::LE,
            VdTraitItemPath::Ge => VdMirBaseSeparator::GE,
            VdTraitItemPath::FieldDiv => todo!(),
            VdTraitItemPath::RealSqrt => todo!(),
        };
        match separator {
            VdMirBaseSeparator::Chaining(separator) => {
                VdBaseChainingSeparatorSignature::new(separator, instantiation, item_ty, expr_ty)
                    .into()
            }
            VdMirBaseSeparator::Folding(separator) => {
                VdBaseFoldingSeparatorSignature::new(separator, instantiation, item_ty, expr_ty)
                    .into()
            }
        }
    }
}

impl VdBaseSeparatorSignature {
    pub fn instantiation(self) -> VdInstantiation {
        match self {
            VdBaseSeparatorSignature::Chaining(slf) => slf.instantiation(),
            VdBaseSeparatorSignature::Folding(slf) => slf.instantiation(),
        }
    }

    pub fn separator(self) -> VdMirBaseSeparator {
        todo!()
        // self.opr
    }

    pub fn item_ty(self) -> VdType {
        todo!()
        // self.item_ty
    }

    pub fn expr_ty(self) -> VdType {
        todo!()
        // self.expr_ty
    }
}
