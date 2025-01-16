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
