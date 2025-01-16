use super::*;
use visored_mir_opr::separator::chaining::VdMirBaseContainmentSeparator;

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, PartialOrd, Ord)]
pub enum VdBaseContainmentSeparatorSignature {
    InSet,
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
}

impl VdBaseContainmentSeparatorSignature {
    pub fn instantiation(self) -> VdInstantiation {
        todo!()
    }

    pub fn separator(self) -> VdMirBaseContainmentSeparator {
        match self {
            VdBaseContainmentSeparatorSignature::InSet => VdMirBaseContainmentSeparator::IN_SET,
        }
    }
}
