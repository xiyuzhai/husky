use super::{default_table::VdBasePrefixOprKey, *};
use crate::menu::VdGlobalDispatchMenu;
use lisp_csv::{
    expr::LpCsvExprData,
    file::{LpCsvFile, LpCsvFileData},
    row::LpCsvRow,
};
use visored_opr::{menu::VdOprMenu, opr::prefix::VdBasePrefixOpr};
use visored_signature::{
    signature::{
        prefix_opr::{VdBasePrefixOprSignature, VdPrefixOprSignature},
        VdSignature,
    },
    table::VdSignatureTable,
};
use visored_term::{menu::VdTypeMenu, ty::VdType};

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

    pub fn collect_from_lisp_csv_files<'a>(
        file: &'a LpCsvFile,
        signature_table: &'a VdSignatureTable,
    ) -> impl Iterator<Item = (VdBasePrefixOprKey, Self)> + 'a {
        let LpCsvFileData::Rows(rows) = file.data();
        rows.iter()
            .map(|row| Self::collect_from_lisp_csv_row(row, signature_table))
    }

    fn collect_from_lisp_csv_row(
        row: &LpCsvRow,
        signature_table: &VdSignatureTable,
    ) -> (VdBasePrefixOprKey, Self) {
        let LpCsvRow::SeparatedExprs(exprs) = row else {
            todo!()
        };
        let &[ref base_opr, ref opd_ty, ref signature_ident] = exprs as &[_] else {
            todo!()
        };
        let base_opr = VdBasePrefixOpr::from_lp_csv_expr(base_opr);
        let opd_ty = VdType::from_lp_csv_expr(opd_ty);
        let LpCsvExprData::Ident(ref signature_ident) = signature_ident.data else {
            todo!()
        };
        let VdSignature::PrefixOpr(VdPrefixOprSignature::Base(signature)) =
            signature_table[signature_ident]
        else {
            todo!()
        };
        let dispatch = VdPrefixOprGlobalDispatch::Base {
            base_opr,
            signature,
        };
        (VdBasePrefixOprKey { base_opr, opd_ty }, dispatch)
    }
}

#[test]
fn vd_prefix_opr_global_dispatch_standard_defaults_works() {
    use crate::default_table::VdDefaultGlobalDispatchTable;
    use crate::menu::{vd_global_dispatch_menu, VdGlobalDispatchMenu};
    use visored_opr::menu::vd_opr_menu;
    use visored_term::menu::VD_TYPE_MENU;

    let table = VdDefaultGlobalDispatchTable::from_standard_lisp_csv_file_dir();
    let zfc_ty_menu = &VD_TYPE_MENU;
    let opr_menu = &vd_opr_menu;
    let global_dispatch_menu = &vd_global_dispatch_menu;
    for ((base_opr, opd_ty), dispatch) in
        VdPrefixOprGlobalDispatch::standard_defaults(&zfc_ty_menu, &opr_menu, &global_dispatch_menu)
    {
        assert_eq!(
            table.base_prefix_opr_default_dispatch(base_opr, opd_ty),
            Some(dispatch)
        );
    }
}
