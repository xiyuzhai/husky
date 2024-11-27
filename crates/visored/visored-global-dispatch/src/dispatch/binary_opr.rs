use super::*;
use crate::{default_table::VdBaseBinaryOprKey, menu::VdGlobalDispatchMenu};
use lisp_csv::{
    expr::LpCsvExprData,
    file::{LpCsvFile, LpCsvFileData},
    row::LpCsvRow,
};
use visored_opr::{menu::VdOprMenu, opr::binary::VdBaseBinaryOpr};
use visored_signature::{
    signature::{
        binary_opr::{base::VdBaseBinaryOprSignature, VdBinaryOprSignature},
        VdSignature,
    },
    table::VdSignatureTable,
};
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

    pub fn collect_from_lisp_csv_files<'a>(
        base_binary_opr_file: &'a LpCsvFile,
        signature_table: &'a VdSignatureTable,
    ) -> impl Iterator<Item = (VdBaseBinaryOprKey, Self)> + 'a {
        let LpCsvFileData::Rows(rows) = base_binary_opr_file.data();
        rows.iter()
            .map(|row| Self::collect_from_lisp_csv_row(row, signature_table))
    }

    pub fn collect_from_lisp_csv_row(
        row: &LpCsvRow,
        signature_table: &VdSignatureTable,
    ) -> (VdBaseBinaryOprKey, Self) {
        let LpCsvRow::SeparatedExprs(exprs) = row else {
            todo!()
        };
        let &[ref lopd_ty, ref base_binary_opr, ref ropd_ty, ref signature_ident] = exprs as &[_]
        else {
            todo!()
        };
        let lopd_ty = VdType::from_lp_csv_expr(lopd_ty);
        let base_binary_opr = VdBaseBinaryOpr::from_lp_csv_expr(base_binary_opr);
        let ropd_ty = VdType::from_lp_csv_expr(ropd_ty);
        let LpCsvExprData::Ident(ref signature_ident) = signature_ident.data else {
            todo!()
        };
        let VdSignature::BinaryOpr(VdBinaryOprSignature::Base(signature)) =
            signature_table[signature_ident]
        else {
            todo!()
        };
        let dispatch = VdBinaryOprGlobalDispatch::Normal {
            base_binary_opr,
            signature,
        };
        (
            VdBaseBinaryOprKey {
                lopd_ty,
                base_binary_opr,
                ropd_ty,
            },
            dispatch,
        )
    }

    pub fn expr_ty(self) -> VdType {
        match self {
            VdBinaryOprGlobalDispatch::Normal { signature, .. } => signature.expr_ty(),
        }
    }
}

#[test]
fn vd_binary_opr_global_dispatch_standard_defaults_works() {
    use crate::default_table::VdDefaultGlobalDispatchTable;
    use crate::menu::{vd_global_dispatch_menu, VdGlobalDispatchMenu};
    use visored_opr::menu::vd_opr_menu;
    use visored_term::menu::VD_TYPE_MENU;

    let table = VdDefaultGlobalDispatchTable::from_standard_lisp_csv_file_dir();
    let ty_menu = &VD_TYPE_MENU;
    let global_dispatch_menu = &vd_global_dispatch_menu;
    let opr_menu = &vd_opr_menu;
    for ((lopd_ty, base_binary_opr, ropd_ty), dispatch) in
        VdBinaryOprGlobalDispatch::standard_defaults(ty_menu, opr_menu, global_dispatch_menu)
    {
        assert_eq!(
            table.base_binary_opr_default_dispatch(lopd_ty, base_binary_opr, ropd_ty),
            Some(dispatch)
        );
    }
}
