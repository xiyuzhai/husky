use visored_opr::{menu::VdOprMenu, opr::prefix::VdBasePrefixOpr};
use visored_signature::signature::prefix_opr::VdBasePrefixOprSignature;
use visored_term::{menu::VdTypeMenu, ty::VdType};

use crate::menu::VdGlobalDispatchMenu;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdPrefixOprGlobalDispatch {
    Base {
        base_opr: VdBasePrefixOpr,
        signature: VdBasePrefixOprSignature,
    },
}
impl VdPrefixOprGlobalDispatch {
    pub fn expr_ty(self) -> visored_term::ty::VdType {
        match self {
            VdPrefixOprGlobalDispatch::Base { signature, .. } => signature.expr_ty(),
        }
    }

    pub(crate) fn standard_defaults(
        zfc_ty_menu: &VdTypeMenu,
        opr_menu: &VdOprMenu,
        global_dispatch_menu: &crate::menu::VdGlobalDispatchMenu,
    ) -> impl IntoIterator<Item = ((VdBasePrefixOpr, VdType), VdPrefixOprGlobalDispatch)> {
        let VdTypeMenu {
            nat,
            int,
            rat,
            real,
            complex,
            ..
        } = *zfc_ty_menu;
        let VdOprMenu { pos, neg, .. } = *opr_menu;
        let VdGlobalDispatchMenu {
            int_pos,
            rat_pos,
            real_pos,
            complex_pos,
            int_neg,
            rat_neg,
            real_neg,
            complex_neg,
            ..
        } = *global_dispatch_menu;
        [
            ((pos, nat), int_pos),
            ((pos, int), int_pos),
            ((pos, rat), rat_pos),
            ((pos, real), real_pos),
            ((pos, complex), complex_pos),
            ((neg, nat), int_neg),
            ((neg, int), int_neg),
            ((neg, rat), rat_neg),
            ((neg, real), real_neg),
            ((neg, complex), complex_neg),
        ]
    }
}
