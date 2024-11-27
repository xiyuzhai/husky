use super::*;
use ::lisp_csv::{
    file::{LpCsvFile, LpCsvFileData},
    parse_lp_csv_file, parse_lp_csv_filepath,
};
use std::path::Path;
use visored_signature::table::VdSignatureTable;

impl VdDefaultGlobalDispatchTable {
    pub fn from_lisp_csv_file_dir(dir: &Path, signature_table: &VdSignatureTable) -> Self {
        let base_prefix_opr_file = dir.join("base_prefix_opr.lpcsv");
        let base_binary_opr_file = dir.join("base_binary_opr.lpcsv");
        let base_separator_file = dir.join("base_separator.lpcsv");
        let power_file = dir.join("power.lpcsv");
        let base_sqrt_file = dir.join("base_sqrt.lpcsv");
        let base_frac_file = dir.join("base_frac.lpcsv");
        let base_chaining_separator_join_file = dir.join("base_chaining_separator_join.lpcsv");
        Self::from_lisp_csv_file_paths(
            &base_prefix_opr_file,
            &base_binary_opr_file,
            &base_separator_file,
            &power_file,
            &base_sqrt_file,
            &base_frac_file,
            &base_chaining_separator_join_file,
            signature_table,
        )
    }

    pub fn from_lisp_csv_file_paths(
        base_prefix_opr_file: &Path,
        base_binary_opr_file: &Path,
        base_separator_file: &Path,
        power_file: &Path,
        base_sqrt_file: &Path,
        base_frac_file: &Path,
        base_chaining_separator_join_file: &Path,
        signature_table: &VdSignatureTable,
    ) -> Self {
        let base_prefix_opr_file = parse_lp_csv_filepath(base_prefix_opr_file).unwrap();
        let base_binary_opr_file = parse_lp_csv_filepath(base_binary_opr_file).unwrap();
        let base_separator_file = parse_lp_csv_filepath(base_separator_file).unwrap();
        let power_file = parse_lp_csv_filepath(power_file).unwrap();
        let base_sqrt_file = parse_lp_csv_filepath(base_sqrt_file).unwrap();
        let base_frac_file = parse_lp_csv_filepath(base_frac_file).unwrap();
        let base_chaining_separator_join_file =
            parse_lp_csv_filepath(base_chaining_separator_join_file).unwrap();
        Self::from_lisp_csv_files(
            &base_prefix_opr_file,
            &base_binary_opr_file,
            &base_separator_file,
            &power_file,
            &base_sqrt_file,
            &base_frac_file,
            &base_chaining_separator_join_file,
            &signature_table,
        )
    }

    pub fn from_lisp_csv_files(
        base_prefix_opr_file: &LpCsvFile,
        base_binary_opr_file: &LpCsvFile,
        base_separator_file: &LpCsvFile,
        power_file: &LpCsvFile,
        base_sqrt_file: &LpCsvFile,
        base_frac_file: &LpCsvFile,
        base_chaining_separator_join_file: &LpCsvFile,
        signature_table: &VdSignatureTable,
    ) -> Self {
        let base_prefix_opr_table = VdPrefixOprGlobalDispatch::collect_from_lisp_csv_files(
            base_prefix_opr_file,
            signature_table,
        );
        let base_binary_opr_table = VdBinaryOprGlobalDispatch::collect_from_lisp_csv_files(
            base_binary_opr_file,
            signature_table,
        );
        let base_separator_table = VdSeparatorGlobalDispatch::collect_from_lisp_csv_files(
            base_separator_file,
            signature_table,
        );
        let power_table =
            VdAttachGlobalDispatch::collect_from_lisp_csv_files(power_file, signature_table);
        let base_sqrt_table =
            VdSqrtGlobalDispatch::collect_from_lisp_csv_files(base_sqrt_file, signature_table);
        let base_frac_table =
            VdFracGlobalDispatch::collect_from_lisp_csv_files(base_frac_file, signature_table);
        let base_chaining_separator_join_default_dispatches =
            VdBaseChainingSeparatorJoinDispatch::collect_from_lisp_csv_files(
                base_chaining_separator_join_file,
                signature_table,
            );
        Self::new(
            base_prefix_opr_table,
            base_binary_opr_table,
            base_separator_table,
            power_table,
            base_sqrt_table,
            base_frac_table,
            base_chaining_separator_join_default_dispatches,
        )
    }
}
