use super::*;
use crate::menu::VdGlobalDispatchMenu;
use default_table::VdBaseSqrtKey;
use lisp_csv::{
    expr::LpCsvExprData,
    file::{LpCsvFile, LpCsvFileData},
    row::LpCsvRow,
};
use visored_signature::{
    signature::{
        sqrt::{VdBaseSqrtSignature, VdSqrtSignature},
        VdSignature,
    },
    table::VdSignatureTable,
};
use visored_term::{menu::VdTypeMenu, ty::VdType};

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdSqrtGlobalDispatch {
    Base { signature: VdBaseSqrtSignature },
}

impl VdSqrtGlobalDispatch {
    pub fn standard_defaults(
        zfc_ty_menu: &VdTypeMenu,
        global_dispatch_menu: &VdGlobalDispatchMenu,
    ) -> impl IntoIterator<Item = (VdType, VdSqrtGlobalDispatch)> {
        let VdTypeMenu {
            nat,
            int,
            rat,
            real,
            complex,
            ..
        } = *zfc_ty_menu;
        let VdGlobalDispatchMenu { real_sqrt, .. } = *global_dispatch_menu;
        [
            (nat, real_sqrt),
            (int, real_sqrt),
            (rat, real_sqrt),
            (real, real_sqrt),
        ]
    }

    pub fn collect_from_lisp_csv_files<'a>(
        file: &'a LpCsvFile,
        signature_table: &'a VdSignatureTable,
    ) -> impl IntoIterator<Item = (VdBaseSqrtKey, VdSqrtGlobalDispatch)> + 'a {
        let LpCsvFileData::Rows(rows) = file.data();
        rows.iter()
            .map(|row| Self::collect_from_csv_row(row, signature_table))
    }

    pub fn collect_from_csv_row(
        row: &LpCsvRow,
        signature_table: &VdSignatureTable,
    ) -> (VdBaseSqrtKey, VdSqrtGlobalDispatch) {
        let LpCsvRow::SeparatedExprs(exprs) = row else {
            todo!()
        };
        let &[ref base_ty, ref signature_ident] = exprs as &[_] else {
            todo!()
        };
        let base_ty = VdType::from_lp_csv_expr(base_ty);
        let LpCsvExprData::Ident(ref signature_ident) = signature_ident.data else {
            todo!()
        };
        let VdSignature::Sqrt(VdSqrtSignature::Base(signature)) = signature_table[signature_ident]
        else {
            todo!()
        };
        let dispatch = VdSqrtGlobalDispatch::Base { signature };
        (VdBaseSqrtKey { base_ty }, dispatch)
    }
}

#[test]
fn vd_sqrt_global_dispatch_standard_defaults_works() {
    use crate::default_table::VdDefaultGlobalDispatchTable;
    use crate::menu::{vd_global_dispatch_menu, VdGlobalDispatchMenu};
    use visored_opr::menu::vd_opr_menu;
    use visored_term::menu::VD_TYPE_MENU;

    let table = VdDefaultGlobalDispatchTable::from_standard_lisp_csv_file_dir();
    let ty_menu = &VD_TYPE_MENU;
    let global_dispatch_menu = &vd_global_dispatch_menu;
    let opr_menu = &vd_opr_menu;
    for ((base_ty), dispatch) in
        VdSqrtGlobalDispatch::standard_defaults(ty_menu, global_dispatch_menu)
    {
        assert_eq!(table.base_sqrt_default_dispatch(base_ty), Some(dispatch));
    }
}
