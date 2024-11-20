use super::*;
use crate::{default_table::VdBaseBinaryOprKey, menu::VdGlobalDispatchMenu};
use visored_opr::{menu::VdOprMenu, opr::binary::VdBaseBinaryOpr};
use visored_signature::signature::binary_opr::base::VdBaseBinaryOprSignature;
use visored_term::{menu::VdTypeMenu, ty::VdType};

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdBinaryOprGlobalDispatch {
    Normal {
        base_binary_opr: VdBaseBinaryOpr,
        signature: VdBaseBinaryOprSignature,
    },
}

impl VdBinaryOprGlobalDispatch {
    pub fn standard_defaults(
        zfc_ty_menu: &VdTypeMenu,
        vd_opr_menu: &VdOprMenu,
        global_dispatch_menu: &VdGlobalDispatchMenu,
    ) -> impl IntoIterator<Item = ((VdType, VdBaseBinaryOpr, VdType), VdBinaryOprGlobalDispatch)>
    {
        let VdTypeMenu {
            nat,
            int,
            rat,
            real,
            complex,
            set,
            prop,
        } = *zfc_ty_menu;
        let VdOprMenu {
            add,
            sub,
            space,
            eq,
            le,
            ge,
            r#in,
            ..
        } = *vd_opr_menu;
        let VdGlobalDispatchMenu {
            int_sub,
            rat_sub,
            real_sub,
            complex_sub,
            ..
        } = *global_dispatch_menu;
        [
            // ## int
            ((nat, sub, nat), int_sub),
            ((nat, sub, int), int_sub),
            ((int, sub, nat), int_sub),
            ((int, sub, int), int_sub),
            // ## rat
            ((nat, sub, rat), rat_sub),
            ((int, sub, rat), rat_sub),
            ((rat, sub, nat), rat_sub),
            ((rat, sub, int), rat_sub),
            ((rat, sub, rat), rat_sub),
            // ## real
            ((nat, sub, real), real_sub),
            ((int, sub, real), real_sub),
            ((rat, sub, real), real_sub),
            ((real, sub, nat), real_sub),
            ((real, sub, int), real_sub),
            ((real, sub, rat), real_sub),
            ((real, sub, real), real_sub),
            // ## complex
            ((nat, sub, complex), complex_sub),
            ((int, sub, complex), complex_sub),
            ((rat, sub, complex), complex_sub),
            ((real, sub, complex), complex_sub),
            ((complex, sub, nat), complex_sub),
            ((complex, sub, int), complex_sub),
            ((complex, sub, rat), complex_sub),
            ((complex, sub, real), complex_sub),
            ((complex, sub, complex), complex_sub),
        ]
    }

    pub fn expr_ty(self) -> VdType {
        match self {
            VdBinaryOprGlobalDispatch::Normal { signature, .. } => signature.expr_ty(),
        }
    }
}
