use super::*;
use crate::menu::VdGlobalDispatchMenu;
use visored_signature::signature::binary_opr::base::VdBaseBinaryOprSignature;
use visored_term::{menu::VdTypeMenu, ty::VdType};

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdFracGlobalDispatch {
    Div { signature: VdBaseBinaryOprSignature },
}

impl VdFracGlobalDispatch {
    pub fn standard_defaults(
        zfc_ty_menu: &VdTypeMenu,
        global_dispatch_menu: &VdGlobalDispatchMenu,
    ) -> impl IntoIterator<Item = ((VdType, VdType), VdFracGlobalDispatch)> {
        let VdTypeMenu {
            nat,
            int,
            rat,
            real,
            complex,
            ..
        } = *zfc_ty_menu;
        let VdGlobalDispatchMenu {
            rat_frac,
            real_frac,
            complex_frac,
            ..
        } = *global_dispatch_menu;
        [
            ((nat, nat), rat_frac),
            ((nat, int), rat_frac),
            ((int, nat), rat_frac),
            ((int, int), rat_frac),
            ((nat, rat), rat_frac),
            ((int, rat), rat_frac),
            ((rat, nat), rat_frac),
            ((rat, int), rat_frac),
            ((rat, rat), rat_frac),
            ((nat, real), real_frac),
            ((int, real), real_frac),
            ((rat, real), real_frac),
            ((real, nat), real_frac),
            ((real, int), real_frac),
            ((real, rat), real_frac),
            ((real, real), real_frac),
            ((nat, complex), complex_frac),
            ((int, complex), complex_frac),
            ((rat, complex), complex_frac),
            ((real, complex), complex_frac),
            ((complex, nat), complex_frac),
            ((complex, int), complex_frac),
            ((complex, rat), complex_frac),
            ((complex, real), complex_frac),
            ((complex, complex), complex_frac),
        ]
    }
}
