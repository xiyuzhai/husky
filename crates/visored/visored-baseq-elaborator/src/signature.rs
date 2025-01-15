use crate::*;
use elaborator::VdBsqElaboratorInner;
use visored_signature::signature::{separator::base::VdBaseSeparatorSignature, VdSignature};
use visored_term::ty::VdType;

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub(crate) fn eq_signature(&self, ty: VdType) -> VdBaseSeparatorSignature {
        let ty_menu = self.ty_menu();
        if ty == ty_menu.nat {
            self.signature_menu().nat_eq
        } else if ty == ty_menu.int {
            self.signature_menu().int_eq
        } else if ty == ty_menu.rat {
            self.signature_menu().rat_eq
        } else if ty == ty_menu.real {
            self.signature_menu().real_eq
        } else if ty == ty_menu.complex {
            self.signature_menu().complex_eq
        } else if ty == ty_menu.prop {
            todo!("prop equivalence")
            // self.signature_menu().vec_eq
        } else {
            todo!("unsupported type: {:?}", ty)
        }
    }
}
