pub mod join;

use super::*;
use crate::menu::VdGlobalDispatchMenu;
use default_table::VdBaseSeparatorKey;
use lisp_csv::{
    expr::LpCsvExprData,
    file::{LpCsvFile, LpCsvFileData},
    row::LpCsvRow,
};
use visored_opr::{menu::VdOprMenu, separator::VdBaseSeparator};
use visored_signature::{
    signature::{
        separator::{base::VdBaseSeparatorSignature, VdSeparatorSignature},
        VdSignature,
    },
    table::VdSignatureTable,
};
use visored_term::{
    menu::{VdTypeMenu, VD_TYPE_MENU},
    ty::VdType,
};

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdSeparatorGlobalDispatch {
    Folding {
        base_separator: VdBaseSeparator,
        signature: VdBaseSeparatorSignature,
    },
    Chaining {
        base_separator: VdBaseSeparator,
        signature: VdBaseSeparatorSignature,
    },
    InSet {
        expr_ty: VdType,
    },
}

impl VdSeparatorGlobalDispatch {
    pub(crate) fn standard_defaults(
        zfc_ty_menu: &VdTypeMenu,
        vd_opr_menu: &VdOprMenu,
        global_dispatch_menu: &VdGlobalDispatchMenu,
    ) -> impl IntoIterator<Item = ((VdType, VdBaseSeparator, VdType), VdSeparatorGlobalDispatch)>
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
            pos,
            neg,
            sub,
            add,
            space,
            eq,
            ne,
            lt,
            gt,
            le,
            ge,
            r#in,
        } = *vd_opr_menu;
        let VdGlobalDispatchMenu {
            int_pos,
            rat_pos,
            real_pos,
            complex_pos,
            int_neg,
            rat_neg,
            real_neg,
            complex_neg,
            int_sub,
            rat_sub,
            real_sub,
            complex_sub,
            rat_div,
            real_div,
            complex_div,
            nat_add,
            int_add,
            rat_add,
            real_add,
            complex_add,
            nat_space_mul,
            int_space_mul,
            rat_space_mul,
            real_space_mul,
            complex_space_mul,
            nat_to_the_power_of_nat,
            int_to_the_power_of_nat,
            rat_to_the_power_of_nat,
            real_to_the_power_of_nat,
            complex_to_the_power_of_nat,
            nat_eq,
            int_eq,
            rat_eq,
            real_eq,
            complex_eq,
            nat_ne,
            int_ne,
            rat_ne,
            real_ne,
            complex_ne,
            nat_lt,
            int_lt,
            rat_lt,
            real_lt,
            nat_gt,
            int_gt,
            rat_gt,
            real_gt,
            nat_le,
            int_le,
            rat_le,
            real_le,
            nat_ge,
            int_ge,
            rat_ge,
            real_ge,
            in_set,
            real_sqrt,
            rat_frac,
            real_frac,
            complex_frac,
        } = *global_dispatch_menu;
        [
            // ## add
            // ### nat
            ((nat, add, nat), nat_add),
            // ### int
            ((nat, add, int), int_add),
            ((int, add, nat), int_add),
            ((int, add, int), int_add),
            // ### rat
            ((nat, add, rat), rat_add),
            ((int, add, rat), rat_add),
            ((rat, add, nat), rat_add),
            ((rat, add, int), rat_add),
            ((rat, add, rat), rat_add),
            // ### real
            ((nat, add, real), real_add),
            ((int, add, real), real_add),
            ((rat, add, real), real_add),
            ((real, add, nat), real_add),
            ((real, add, int), real_add),
            ((real, add, rat), real_add),
            ((real, add, real), real_add),
            // ### complex
            ((nat, add, complex), complex_add),
            ((int, add, complex), complex_add),
            ((rat, add, complex), complex_add),
            ((real, add, complex), complex_add),
            ((complex, add, nat), complex_add),
            ((complex, add, int), complex_add),
            ((complex, add, rat), complex_add),
            ((complex, add, real), complex_add),
            ((complex, add, complex), complex_add),
            // ## mul
            // ### nat
            ((nat, space, nat), nat_space_mul),
            // ### int
            ((nat, space, int), int_space_mul),
            ((int, space, nat), int_space_mul),
            ((int, space, int), int_space_mul),
            // ### rat
            ((nat, space, rat), rat_space_mul),
            ((int, space, rat), rat_space_mul),
            ((rat, space, nat), rat_space_mul),
            ((rat, space, int), rat_space_mul),
            ((rat, space, rat), rat_space_mul),
            // ### real
            ((nat, space, real), real_space_mul),
            ((int, space, real), real_space_mul),
            ((rat, space, real), real_space_mul),
            ((real, space, nat), real_space_mul),
            ((real, space, int), real_space_mul),
            ((real, space, rat), real_space_mul),
            ((real, space, real), real_space_mul),
            // ### complex
            ((nat, space, complex), complex_space_mul),
            ((int, space, complex), complex_space_mul),
            ((rat, space, complex), complex_space_mul),
            ((real, space, complex), complex_space_mul),
            ((complex, space, nat), complex_space_mul),
            ((complex, space, int), complex_space_mul),
            ((complex, space, rat), complex_space_mul),
            ((complex, space, real), complex_space_mul),
            ((complex, space, complex), complex_space_mul),
            // ## eq
            // ### nat
            ((nat, eq, nat), nat_eq),
            // ### int
            ((nat, eq, int), int_eq),
            ((int, eq, nat), int_eq),
            ((int, eq, int), int_eq),
            // ### rat
            ((nat, eq, rat), rat_eq),
            ((int, eq, rat), rat_eq),
            ((rat, eq, nat), rat_eq),
            ((rat, eq, int), rat_eq),
            ((rat, eq, rat), rat_eq),
            // ### real
            ((nat, eq, real), real_eq),
            ((int, eq, real), real_eq),
            ((rat, eq, real), real_eq),
            ((real, eq, nat), real_eq),
            ((real, eq, int), real_eq),
            ((real, eq, rat), real_eq),
            ((real, eq, real), real_eq),
            // ### complex
            ((nat, eq, complex), complex_eq),
            ((rat, eq, complex), complex_eq),
            ((int, eq, complex), complex_eq),
            ((real, eq, complex), complex_eq),
            ((complex, eq, nat), complex_eq),
            ((complex, eq, rat), complex_eq),
            ((complex, eq, int), complex_eq),
            ((complex, eq, real), complex_eq),
            ((complex, eq, complex), complex_eq),
            // ## ne
            // ### nat
            ((nat, ne, nat), nat_ne),
            // ### int
            ((nat, ne, int), int_ne),
            ((int, ne, nat), int_ne),
            ((int, ne, int), int_ne),
            // ### rat
            ((nat, ne, rat), rat_ne),
            ((int, ne, rat), rat_ne),
            ((rat, ne, nat), rat_ne),
            ((rat, ne, int), rat_ne),
            ((rat, ne, rat), rat_ne),
            // ### real
            ((nat, ne, real), real_ne),
            ((int, ne, real), real_ne),
            ((rat, ne, real), real_ne),
            ((real, ne, nat), real_ne),
            ((real, ne, int), real_ne),
            ((real, ne, rat), real_ne),
            ((real, ne, real), real_ne),
            // ### complex
            ((nat, ne, complex), complex_ne),
            ((rat, ne, complex), complex_ne),
            ((int, ne, complex), complex_ne),
            ((real, ne, complex), complex_ne),
            ((complex, ne, nat), complex_ne),
            ((complex, ne, rat), complex_ne),
            ((complex, ne, int), complex_ne),
            ((complex, ne, real), complex_ne),
            ((complex, ne, complex), complex_ne),
            // ## lt
            // ### nat
            ((nat, lt, nat), nat_lt),
            // ### int
            ((nat, lt, int), int_lt),
            ((int, lt, nat), int_lt),
            ((int, lt, int), int_lt),
            // ### rat
            ((nat, lt, rat), rat_lt),
            ((int, lt, rat), rat_lt),
            ((rat, lt, nat), rat_lt),
            ((rat, lt, int), rat_lt),
            ((rat, lt, rat), rat_lt),
            // ### real
            ((nat, lt, real), real_lt),
            ((int, lt, real), real_lt),
            ((rat, lt, real), real_lt),
            ((real, lt, nat), real_lt),
            ((real, lt, int), real_lt),
            ((real, lt, rat), real_lt),
            ((real, lt, real), real_lt),
            // ## gt
            // ### nat
            ((nat, gt, nat), nat_gt),
            // ### int
            ((nat, gt, int), int_gt),
            ((int, gt, nat), int_gt),
            ((int, gt, int), int_gt),
            // ### rat
            ((nat, gt, rat), rat_gt),
            ((int, gt, rat), rat_gt),
            ((rat, gt, nat), rat_gt),
            ((rat, gt, int), rat_gt),
            ((rat, gt, rat), rat_gt),
            // ### real
            ((nat, gt, real), real_gt),
            ((int, gt, real), real_gt),
            ((rat, gt, real), real_gt),
            ((real, gt, nat), real_gt),
            ((real, gt, int), real_gt),
            ((real, gt, rat), real_gt),
            ((real, gt, real), real_gt),
            // ## le
            // ### nat
            ((nat, le, nat), nat_le),
            // ### int
            ((nat, le, int), int_le),
            ((int, le, nat), int_le),
            ((int, le, int), int_le),
            // ### rat
            ((nat, le, rat), rat_le),
            ((int, le, rat), rat_le),
            ((rat, le, nat), rat_le),
            ((rat, le, int), rat_le),
            ((rat, le, rat), rat_le),
            // ### real
            ((nat, le, real), real_le),
            ((int, le, real), real_le),
            ((rat, le, real), real_le),
            ((real, le, nat), real_le),
            ((real, le, int), real_le),
            ((real, le, rat), real_le),
            ((real, le, real), real_le),
            // ## ge
            // ### nat
            ((nat, ge, nat), nat_ge),
            // ### int
            ((nat, ge, int), int_ge),
            ((int, ge, nat), int_ge),
            ((int, ge, int), int_ge),
            // ### rat
            ((nat, ge, rat), rat_ge),
            ((int, ge, rat), rat_ge),
            ((rat, ge, nat), rat_ge),
            ((rat, ge, int), rat_ge),
            ((rat, ge, rat), rat_ge),
            // ### real
            ((nat, ge, real), real_ge),
            ((int, ge, real), real_ge),
            ((rat, ge, real), real_ge),
            ((real, ge, nat), real_ge),
            ((real, ge, int), real_ge),
            ((real, ge, rat), real_ge),
            ((real, ge, real), real_ge),
            // ## in
            ((nat, r#in, set), in_set),
            ((int, r#in, set), in_set),
            ((rat, r#in, set), in_set),
            ((real, r#in, set), in_set),
            ((complex, r#in, set), in_set),
        ]
    }

    pub fn collect_from_lisp_csv_files<'a>(
        base_separator_file: &'a LpCsvFile,
        signature_table: &'a VdSignatureTable,
    ) -> impl Iterator<Item = (VdBaseSeparatorKey, Self)> + 'a {
        let LpCsvFileData::Rows(rows) = base_separator_file.data();
        rows.iter()
            .map(|row| Self::collect_from_lisp_csv_row(row, signature_table))
    }

    fn collect_from_lisp_csv_row(
        row: &LpCsvRow,
        signature_table: &VdSignatureTable,
    ) -> (VdBaseSeparatorKey, Self) {
        let LpCsvRow::SeparatedExprs(exprs) = row else {
            todo!()
        };
        let &[ref prev_item_ty, ref base_separator, ref next_item_ty, ref dispatch] =
            exprs as &[_]
        else {
            todo!()
        };
        let base_separator = VdBaseSeparator::from_lp_csv_expr(base_separator);
        let (ref dispatch_variant, ref dispatch_arguments) = dispatch.application_expansion();
        let LpCsvExprData::Ident(ref dispatch_variant_ident) = dispatch_variant.data else {
            todo!()
        };
        let prev_item_ty = VdType::from_lp_csv_expr(prev_item_ty);
        let next_item_ty = VdType::from_lp_csv_expr(next_item_ty);
        let key = VdBaseSeparatorKey {
            base_separator,
            prev_item_ty,
            next_item_ty,
        };
        let dispatch = match dispatch_variant_ident.as_str() {
            "folding" => {
                let [ref signature] = dispatch_arguments else {
                    todo!()
                };
                let LpCsvExprData::Ident(ref signature_ident) = signature.data else {
                    todo!()
                };
                let VdSignature::Separator(VdSeparatorSignature::Base(signature)) =
                    signature_table[signature_ident]
                else {
                    todo!()
                };
                VdSeparatorGlobalDispatch::Folding {
                    base_separator,
                    signature,
                }
            }
            "chaining" => {
                let [ref signature] = dispatch_arguments else {
                    todo!()
                };
                let LpCsvExprData::Ident(ref signature_ident) = signature.data else {
                    todo!()
                };
                let VdSignature::Separator(VdSeparatorSignature::Base(signature)) =
                    signature_table[signature_ident]
                else {
                    todo!()
                };
                VdSeparatorGlobalDispatch::Chaining {
                    base_separator,
                    signature,
                }
            }
            "in_set" => VdSeparatorGlobalDispatch::InSet {
                expr_ty: VD_TYPE_MENU.prop,
            },
            ident => todo!("ident: {ident} not handled"),
        };
        (key, dispatch)
    }
}

#[test]
fn vd_separator_global_dispatch_standard_defaults_works() {
    use crate::default_table::VdDefaultGlobalDispatchTable;
    use crate::menu::{vd_global_dispatch_menu, VdGlobalDispatchMenu};
    use visored_opr::menu::vd_opr_menu;
    use visored_term::menu::VD_TYPE_MENU;

    let table = VdDefaultGlobalDispatchTable::from_standard_lisp_csv_file_dir();
    let ty_menu = &VD_TYPE_MENU;
    let global_dispatch_menu = &vd_global_dispatch_menu;
    let opr_menu = &vd_opr_menu;
    for ((prev_item_ty, base_separator, next_item_ty), dispatch) in
        VdSeparatorGlobalDispatch::standard_defaults(&ty_menu, &opr_menu, &global_dispatch_menu)
    {
        assert_eq!(
            table.base_separator_default_dispatch(prev_item_ty, base_separator, next_item_ty),
            Some(dispatch)
        );
    }
}
