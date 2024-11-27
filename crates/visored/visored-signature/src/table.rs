use std::path::Path;

use crate::signature::VdSignature;
use crate::*;
use lisp_csv::{expr::LpCsvExprData, file::LpCsvFile, row::LpCsvRow};
use lisp_csv::{file::LpCsvFileData, parse_lp_csv_file};
use menu::{vd_signature_menu, VdSignatureMenu};
use rustc_hash::FxHashMap;
use salsa::DebugWithDb;

#[salsa::derive_debug_with_db]
#[derive(Debug)]
pub struct VdSignatureTable {
    table: FxHashMap<String, VdSignature>,
}

impl std::ops::Index<&str> for VdSignatureTable {
    type Output = VdSignature;

    #[track_caller]
    fn index(&self, key: &str) -> &Self::Output {
        match self.table.get(key) {
            Some(signature) => signature,
            None => todo!("key = {key:?} not found in table"),
        }
    }
}

impl VdSignatureTable {
    pub fn new(data: impl IntoIterator<Item = (String, VdSignature)>) -> Self {
        let mut table = FxHashMap::default();
        for (key, signature) in data {
            if table.contains_key(&key) {
                todo!()
            } else {
                table.insert(key, signature);
            }
        }
        Self { table }
    }

    pub fn from_lp_csv_file_path(path: &Path) -> Self {
        let file = std::fs::read_to_string(path).unwrap();
        let file = parse_lp_csv_file(&file).unwrap();
        Self::from_lp_csv_file(&file)
    }

    pub fn from_lp_csv_file(file: &LpCsvFile) -> Self {
        match file.data() {
            LpCsvFileData::Rows(rows) => Self::from_lp_csv_rows(&rows),
        }
    }

    fn from_lp_csv_rows(rows: &[LpCsvRow]) -> Self {
        let mut table: FxHashMap<String, VdSignature> = FxHashMap::default();
        assert!(!rows.is_empty());
        for row in rows {
            let (ident, signature) = match row {
                LpCsvRow::Expr(expr) => todo!(),
                LpCsvRow::SeparatedExprs(exprs) => {
                    assert_eq!(exprs.len(), 3);
                    let ident = match exprs[0].data {
                        LpCsvExprData::Ident(ref ident) => ident.to_string(),
                        _ => todo!(),
                    };
                    let signature = VdSignature::from_lp_csv_exprs(&exprs[1..]);
                    (ident, signature)
                }
            };
            if table.contains_key(&ident) {
                todo!()
            } else {
                table.insert(ident, signature);
            }
        }
        assert!(!table.is_empty());
        Self { table }
    }
}

#[test]
fn vd_signature_table_from_lp_csv_rows_works() {
    use husky_path_utils::HuskyLangDevPaths;

    let dev_dirs = HuskyLangDevPaths::new();
    let file = std::fs::read_to_string(dev_dirs.specs_dir().join("visored/signature_table.lpcsv"))
        .unwrap();
    let file = parse_lp_csv_file(&file).unwrap();
    let table = VdSignatureTable::from_lp_csv_file(&file);
    expect_file!["../expect-files/signature_table.debug.txt"].assert_debug_eq(&table);
    let VdSignatureMenu {
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
        nat_mul,
        int_mul,
        rat_mul,
        real_mul,
        complex_mul,
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
        real_sqrt,
    } = *vd_signature_menu;
    let entries: Vec<(&str, VdSignature)> = vec![
        ("int_pos", int_pos.into()),
        ("rat_pos", rat_pos.into()),
        ("real_pos", real_pos.into()),
        ("complex_pos", complex_pos.into()),
        ("int_neg", int_neg.into()),
        ("rat_neg", rat_neg.into()),
        ("real_neg", real_neg.into()),
        ("complex_neg", complex_neg.into()),
        ("int_sub", int_sub.into()),
        ("rat_sub", rat_sub.into()),
        ("real_sub", real_sub.into()),
        ("complex_sub", complex_sub.into()),
        ("rat_div", rat_div.into()),
        ("real_div", real_div.into()),
        ("complex_div", complex_div.into()),
        ("nat_add", nat_add.into()),
        ("int_add", int_add.into()),
        ("rat_add", rat_add.into()),
        ("real_add", real_add.into()),
        ("complex_add", complex_add.into()),
        ("nat_mul", nat_mul.into()),
        ("int_mul", int_mul.into()),
        ("rat_mul", rat_mul.into()),
        ("real_mul", real_mul.into()),
        ("complex_mul", complex_mul.into()),
        ("nat_to_the_power_of_nat", nat_to_the_power_of_nat.into()),
        ("int_to_the_power_of_nat", int_to_the_power_of_nat.into()),
        ("rat_to_the_power_of_nat", rat_to_the_power_of_nat.into()),
        ("real_to_the_power_of_nat", real_to_the_power_of_nat.into()),
        (
            "complex_to_the_power_of_nat",
            complex_to_the_power_of_nat.into(),
        ),
        ("nat_eq", nat_eq.into()),
        ("int_eq", int_eq.into()),
        ("rat_eq", rat_eq.into()),
        ("real_eq", real_eq.into()),
        ("complex_eq", complex_eq.into()),
        ("nat_ne", nat_ne.into()),
        ("int_ne", int_ne.into()),
        ("rat_ne", rat_ne.into()),
        ("real_ne", real_ne.into()),
        ("complex_ne", complex_ne.into()),
        ("nat_lt", nat_lt.into()),
        ("int_lt", int_lt.into()),
        ("rat_lt", rat_lt.into()),
        ("real_lt", real_lt.into()),
        ("nat_gt", nat_gt.into()),
        ("int_gt", int_gt.into()),
        ("rat_gt", rat_gt.into()),
        ("real_gt", real_gt.into()),
        ("nat_le", nat_le.into()),
        ("int_le", int_le.into()),
        ("rat_le", rat_le.into()),
        ("real_le", real_le.into()),
        ("nat_ge", nat_ge.into()),
        ("int_ge", int_ge.into()),
        ("rat_ge", rat_ge.into()),
        ("real_ge", real_ge.into()),
        ("real_sqrt", real_sqrt.into()),
    ];
    for (key, signature) in entries {
        assert_eq!(
            table[key], signature,
            "table[key] = {:#?}, signature = {:#?}",
            table[key], signature
        );
    }
}
