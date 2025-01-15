use crate::*;
use elaborator::VdBsqElaboratorInner;
use visored_signature::signature::{separator::base::VdBaseSeparatorSignature, VdSignature};
use visored_term::ty::VdType;

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub(crate) fn eq_signature(&self, ty: VdType) -> VdBaseSeparatorSignature {
        let ty_menu = self.ty_menu();
        let signature_menu = self.signature_menu();
        if ty == ty_menu.nat {
            signature_menu.nat_eq
        } else if ty == ty_menu.int {
            signature_menu.int_eq
        } else if ty == ty_menu.rat {
            signature_menu.rat_eq
        } else if ty == ty_menu.real {
            signature_menu.real_eq
        } else if ty == ty_menu.complex {
            signature_menu.complex_eq
        } else if ty == ty_menu.prop {
            todo!("prop equivalence")
            // self.signature_menu().vec_eq
        } else {
            todo!("unsupported type: {:?}", ty)
        }
    }

    pub(crate) fn add_signature(
        &self,
        leader_ty: VdType,
        follower_ty: VdType,
    ) -> VdBaseSeparatorSignature {
        let ty_menu = self.ty_menu();
        let signature_menu = self.signature_menu();
        if leader_ty == ty_menu.nat && follower_ty == ty_menu.nat {
            signature_menu.nat_add
        } else if leader_ty == ty_menu.int && follower_ty == ty_menu.int {
            signature_menu.int_add
        } else if leader_ty == ty_menu.rat && follower_ty == ty_menu.rat {
            signature_menu.rat_add
        } else if leader_ty == ty_menu.real && follower_ty == ty_menu.real {
            signature_menu.real_add
        } else if leader_ty == ty_menu.complex && follower_ty == ty_menu.complex {
            signature_menu.complex_add
        } else {
            todo!()
        }
    }

    pub(crate) fn mul_signature(
        &self,
        leader_ty: VdType,
        follower_ty: VdType,
    ) -> VdBaseSeparatorSignature {
        let ty_menu = self.ty_menu();
        let signature_menu = self.signature_menu();
        if leader_ty == ty_menu.nat && follower_ty == ty_menu.nat {
            signature_menu.nat_mul
        } else if leader_ty == ty_menu.int && follower_ty == ty_menu.int {
            signature_menu.int_mul
        } else if leader_ty == ty_menu.rat && follower_ty == ty_menu.rat {
            signature_menu.rat_mul
        } else if leader_ty == ty_menu.real && follower_ty == ty_menu.real {
            signature_menu.real_mul
        } else if leader_ty == ty_menu.complex && follower_ty == ty_menu.complex {
            signature_menu.complex_mul
        } else {
            todo!("unsupported type: {:?} {:?}", leader_ty, follower_ty)
        }
    }
}
