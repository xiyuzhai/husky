use super::*;
use visored_entity_path::path::{trai_item::VdTraitItemPath, VdItemPath};
use visored_mir_opr::opr::prefix::VdMirBasePrefixOpr;

#[salsa::derive_debug_with_db]
#[enum_class::from_variants]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdPrefixOprSignature {
    Base(VdBasePrefixOprSignature),
}

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, PartialOrd, Ord)]
pub struct VdBasePrefixOprSignature {
    pub instantiation: VdInstantiation,
    // TODO: replace this with something more ethereal
    pub opr: VdMirBasePrefixOpr,
    pub opd_ty: VdType,
    pub expr_ty: VdType,
}

impl From<VdBasePrefixOprSignature> for VdSignature {
    fn from(signature: VdBasePrefixOprSignature) -> Self {
        VdSignature::PrefixOpr(VdPrefixOprSignature::Base(signature))
    }
}

impl VdBasePrefixOprSignature {
    pub fn new(instantiation: VdInstantiation, opd_ty: VdType, expr_ty: VdType) -> Self {
        let VdItemPath::TraitItem(path) = instantiation.path() else {
            unreachable!()
        };
        let opr = match path {
            VdTraitItemPath::Iff => todo!(),
            VdTraitItemPath::GroupMul => todo!(),
            VdTraitItemPath::AbelianGroupAdd => todo!(),
            VdTraitItemPath::NatAdd => todo!(),
            VdTraitItemPath::NatMul => todo!(),
            VdTraitItemPath::CommRingAdd => todo!(),
            VdTraitItemPath::CommRingSub => todo!(),
            VdTraitItemPath::CommRingMul => todo!(),
            VdTraitItemPath::CommRingPower => todo!(),
            VdTraitItemPath::CommRingPos => VdMirBasePrefixOpr::RING_POS,
            VdTraitItemPath::CommRingNeg => VdMirBasePrefixOpr::RING_NEG,
            VdTraitItemPath::Eq => todo!(),
            VdTraitItemPath::Ne => todo!(),
            VdTraitItemPath::Lt => todo!(),
            VdTraitItemPath::Gt => todo!(),
            VdTraitItemPath::Le => todo!(),
            VdTraitItemPath::Ge => todo!(),
            VdTraitItemPath::FieldDiv => todo!(),
            VdTraitItemPath::RealSqrt => todo!(),
        };
        Self {
            instantiation,
            opr,
            opd_ty,
            expr_ty,
        }
    }
}

impl VdBasePrefixOprSignature {
    pub fn instantiation(self) -> VdInstantiation {
        self.instantiation
    }

    pub fn opd_ty(self) -> VdType {
        self.opd_ty
    }

    pub fn expr_ty(self) -> VdType {
        self.expr_ty
    }
}
