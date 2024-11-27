use super::*;
use crate::menu::VdGlobalDispatchMenu;
use default_table::VdBaseFracKey;
use lisp_csv::{
    expr::LpCsvExprData,
    file::{LpCsvFile, LpCsvFileData},
    row::LpCsvRow,
};
use visored_signature::{
    signature::{
        binary_opr::{base::VdBaseBinaryOprSignature, VdBinaryOprSignature},
        VdSignature,
    },
    table::VdSignatureTable,
};
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

    pub fn collect_from_lisp_csv_files<'a>(
        file: &'a LpCsvFile,
        signature_table: &'a VdSignatureTable,
    ) -> impl IntoIterator<Item = (VdBaseFracKey, VdFracGlobalDispatch)> + 'a {
        let LpCsvFileData::Rows(rows) = file.data();
        rows.iter()
            .map(|row| Self::collect_from_csv_row(row, signature_table))
    }

    pub fn collect_from_csv_row(
        row: &LpCsvRow,
        signature_table: &VdSignatureTable,
    ) -> (VdBaseFracKey, Self) {
        let LpCsvRow::SeparatedExprs(exprs) = row else {
            todo!()
        };
        let &[ref numerator_ty, ref denominator_ty, ref signature_ident] = exprs as &[_] else {
            todo!()
        };
        let numerator_ty = VdType::from_lp_csv_expr(numerator_ty);
        let denominator_ty = VdType::from_lp_csv_expr(denominator_ty);
        let LpCsvExprData::Ident(ref signature_ident) = signature_ident.data else {
            todo!()
        };
        let VdSignature::BinaryOpr(VdBinaryOprSignature::Base(signature)) =
            signature_table[signature_ident]
        else {
            todo!()
        };
        let dispatch = VdFracGlobalDispatch::Div { signature };
        (
            VdBaseFracKey {
                numerator_ty,
                denominator_ty,
            },
            dispatch,
        )
    }
}

#[test]
fn vd_frac_global_dispatch_standard_defaults_works() {
    use crate::default_table::VdDefaultGlobalDispatchTable;
    use crate::menu::{vd_global_dispatch_menu, VdGlobalDispatchMenu};
    use visored_opr::menu::vd_opr_menu;
    use visored_term::menu::VD_TYPE_MENU;

    let table = VdDefaultGlobalDispatchTable::from_standard_lisp_csv_file_dir();
    let ty_menu = &VD_TYPE_MENU;
    let global_dispatch_menu = &vd_global_dispatch_menu;
    let opr_menu = &vd_opr_menu;
    for ((numerator_ty, denominator_ty), dispatch) in
        VdFracGlobalDispatch::standard_defaults(ty_menu, global_dispatch_menu)
    {
        assert_eq!(
            table.base_frac_default_dispatch(numerator_ty, denominator_ty),
            Some(dispatch)
        );
    }
}
