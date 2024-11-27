use super::*;
use lisp_csv::expr::LpCsvExpr;
use visored_signature::signature::separator::base::VdBaseSeparatorSignature;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VdBaseChainingSeparatorJoinKey {
    pub prev: VdBaseSeparatorSignature,
    pub next: VdBaseSeparatorSignature,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VdBaseChainingSeparatorJoinDispatch {
    Ok {
        base_separator: VdBaseSeparator,
        signature: VdBaseSeparatorSignature,
    },
    Err,
}

impl VdBaseChainingSeparatorJoinDispatch {
    pub fn collect_from_lisp_csv_files<'a>(
        file: &'a LpCsvFile,
        signature_table: &'a VdSignatureTable,
    ) -> impl IntoIterator<Item = (VdBaseChainingSeparatorJoinKey, Self)> + 'a {
        let LpCsvFileData::Rows(rows) = file.data();
        rows.iter()
            .map(|row| Self::collect_from_csv_row(row, signature_table))
    }

    pub fn collect_from_csv_row(
        row: &LpCsvRow,
        signature_table: &VdSignatureTable,
    ) -> (VdBaseChainingSeparatorJoinKey, Self) {
        let LpCsvRow::SeparatedExprs(exprs) = row else {
            todo!()
        };
        let &[ref prev_signature, ref next_signature, ref dispatch] = exprs as &[LpCsvExpr] else {
            todo!()
        };
        let LpCsvExprData::Ident(ref prev_signature_ident) = prev_signature.data else {
            todo!()
        };
        let VdSignature::Separator(VdSeparatorSignature::Base(prev_signature)) =
            signature_table[prev_signature_ident]
        else {
            todo!()
        };
        let LpCsvExprData::Ident(ref next_signature_ident) = next_signature.data else {
            todo!()
        };
        let VdSignature::Separator(VdSeparatorSignature::Base(next_signature)) =
            signature_table[next_signature_ident]
        else {
            todo!()
        };
        let (dispatch_variant, dispatch_args) = dispatch.application_expansion();
        let LpCsvExprData::Ident(ref dispatch_variant_ident) = dispatch_variant.data else {
            todo!()
        };
        match dispatch_variant_ident.as_str() {
            "ok" => {
                let &[ref base_separator, ref signature] = dispatch_args else {
                    todo!()
                };
                let base_separator = VdBaseSeparator::from_lp_csv_expr(base_separator);
                let LpCsvExprData::Ident(ref signature_ident) = signature.data else {
                    todo!()
                };
                let VdSignature::Separator(VdSeparatorSignature::Base(signature)) =
                    signature_table[signature_ident]
                else {
                    todo!()
                };
                (
                    VdBaseChainingSeparatorJoinKey {
                        prev: prev_signature,
                        next: next_signature,
                    },
                    VdBaseChainingSeparatorJoinDispatch::Ok {
                        base_separator,
                        signature,
                    },
                )
            }
            "err" => todo!(),
            s => todo!("s = {s:?} not handled"),
        }
    }
}
