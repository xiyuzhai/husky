use super::*;
use visored_entity_path::path::{trai_item::VdTraitItemPath, VdItemPath};
use visored_mir_opr::opr::binary::VdMirBaseBinaryOpr;

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, PartialOrd, Ord)]
pub struct VdBaseBinaryOprSignature {
    pub instantiation: VdInstantiation,
    // TODO: replace this with something more ethereal
    pub opr: VdMirBaseBinaryOpr,
    pub lopd_ty: VdType,
    pub ropd_ty: VdType,
    pub expr_ty: VdType,
}

impl From<VdBaseBinaryOprSignature> for VdSignature {
    fn from(signature: VdBaseBinaryOprSignature) -> Self {
        VdSignature::BinaryOpr(signature.into())
    }
}

impl VdBaseBinaryOprSignature {
    pub fn new(
        instantiation: VdInstantiation,
        lopd_ty: VdType,
        ropd_ty: VdType,
        expr_ty: VdType,
    ) -> Self {
        let VdItemPath::TraitItem(path) = instantiation.path() else {
            unreachable!()
        };
        let opr = match path {
            VdTraitItemPath::Iff => todo!(),
            VdTraitItemPath::InSet => todo!(),
            VdTraitItemPath::GroupMul => todo!(),
            VdTraitItemPath::AbelianGroupAdd => todo!(),
            VdTraitItemPath::NatAdd => todo!(),
            VdTraitItemPath::NatMul => todo!(),
            VdTraitItemPath::CommRingAdd => todo!(),
            VdTraitItemPath::CommRingSub => VdMirBaseBinaryOpr::COMM_RING_SUB,
            VdTraitItemPath::CommRingMul => todo!(),
            VdTraitItemPath::CommRingPower => todo!(),
            VdTraitItemPath::CommRingPos => todo!(),
            VdTraitItemPath::CommRingNeg => todo!(),
            VdTraitItemPath::Eq => todo!(),
            VdTraitItemPath::Ne => todo!(),
            VdTraitItemPath::Lt => todo!(),
            VdTraitItemPath::Gt => todo!(),
            VdTraitItemPath::Le => todo!(),
            VdTraitItemPath::Ge => todo!(),
            VdTraitItemPath::FieldDiv => VdMirBaseBinaryOpr::COMM_FIELD_DIV,
            VdTraitItemPath::RealSqrt => todo!(),
        };
        Self {
            instantiation,
            opr,
            lopd_ty,
            ropd_ty,
            expr_ty,
        }
    }
}

impl VdBaseBinaryOprSignature {
    pub fn instantiation(self) -> VdInstantiation {
        self.instantiation
    }

    pub fn lopd_ty(self) -> VdType {
        self.lopd_ty
    }

    pub fn ropd_ty(self) -> VdType {
        self.ropd_ty
    }

    pub fn expr_ty(self) -> VdType {
        self.expr_ty
    }

    pub fn argument_expected_ty(self, i: usize) -> VdType {
        assert!(i == 0 || i == 1);
        if i == 0 {
            self.lopd_ty
        } else {
            self.ropd_ty
        }
    }
}
