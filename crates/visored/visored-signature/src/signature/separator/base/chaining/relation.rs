pub mod comparison;
pub mod containment;

use self::{comparison::*, containment::*};
use super::*;
use visored_mir_opr::separator::chaining::VdMirBaseRelationSeparator;

#[enum_class::from_variants]
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, PartialOrd, Ord)]
pub enum VdBaseRelationSeparatorSignature {
    Containment(VdBaseContainmentSeparatorSignature),
    Comparison(VdBaseComparisonSeparatorSignature),
}

impl VdBaseRelationSeparatorSignature {
    pub const IN_SET: Self = Self::Containment(VdBaseContainmentSeparatorSignature::InSet);
}

impl VdBaseRelationSeparatorSignature {
    pub fn new(
        separator: VdMirBaseRelationSeparator,
        instantiation: VdInstantiation,
        item_ty: VdType,
        expr_ty: VdType,
    ) -> Self {
        match separator {
            VdMirBaseRelationSeparator::Containment(separator) => {
                VdBaseContainmentSeparatorSignature::new(separator, instantiation, item_ty, expr_ty)
                    .into()
            }
            VdMirBaseRelationSeparator::Comparison(separator) => {
                VdBaseComparisonSeparatorSignature::new(separator, instantiation, item_ty, expr_ty)
                    .into()
            }
        }
    }
}

impl VdBaseRelationSeparatorSignature {
    pub fn separator(self) -> VdMirBaseRelationSeparator {
        match self {
            VdBaseRelationSeparatorSignature::Containment(signature) => {
                signature.separator().into()
            }
            VdBaseRelationSeparatorSignature::Comparison(signature) => signature.separator().into(),
        }
    }

    pub fn expr_ty(self) -> VdType {
        match self {
            VdBaseRelationSeparatorSignature::Containment(slf) => todo!(),
            VdBaseRelationSeparatorSignature::Comparison(slf) => slf.expr_ty(),
        }
    }

    pub fn item_ty(self) -> VdType {
        match self {
            VdBaseRelationSeparatorSignature::Containment(slf) => todo!(),
            VdBaseRelationSeparatorSignature::Comparison(slf) => slf.item_ty(),
        }
    }
}
