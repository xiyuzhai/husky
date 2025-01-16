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

impl VdBaseChainingSeparatorSignature {
    pub fn new(
        separator: VdMirBaseChainingSeparator,
        instantiation: VdInstantiation,
        item_ty: VdType,
        expr_ty: VdType,
    ) -> Self {
        match separator {
            VdMirBaseChainingSeparator::Iff => todo!(),
            VdMirBaseChainingSeparator::Relation(separator) => {
                VdBaseRelationSeparatorSignature::new(separator, instantiation, item_ty, expr_ty)
                    .into()
            }
        }
    }
}
