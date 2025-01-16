pub mod attach;
pub mod binary_opr;
pub mod frac;
pub mod function;
pub mod prefix_opr;
pub mod separator;
pub mod sqrt;
pub mod suffix_opr;

use self::{
    attach::*,
    binary_opr::{base::*, composite::*, *},
    frac::*,
    function::*,
    prefix_opr::*,
    separator::*,
    sqrt::*,
};
use crate::*;
use eterned::db::EternerDb;
use lisp_csv::expr::{LpCsvExpr, LpCsvExprData};
use separator::base::{
    chaining::relation::containment::VdBaseContainmentSeparatorSignature, VdBaseSeparatorSignature,
};

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdSignature {
    Attach(VdAttachSignature),
    BinaryOpr(VdBinaryOprSignature),
    Frac(VdFracSignature),
    Function(VdFunctionSignature),
    PrefixOpr(VdPrefixOprSignature),
    Separator(VdSeparatorSignature),
    Sqrt(VdSqrtSignature),
}

impl VdSignature {
    pub fn from_lp_csv_exprs(exprs: &[LpCsvExpr], db: &EternerDb) -> Self {
        assert_eq!(exprs.len(), 2);
        let instantiation = VdInstantiation::from_lp_csv_expr(&exprs[0], db);
        let (
            LpCsvExpr {
                data: LpCsvExprData::Ident(variant_ident),
                ..
            },
            args,
        ) = exprs[1].application_expansion()
        else {
            unreachable!()
        };
        match variant_ident.as_str() {
            "base_prefix_opr" => {
                assert_eq!(args.len(), 2);
                VdBasePrefixOprSignature::new(
                    instantiation,
                    VdType::from_lp_csv_expr(&args[0], db),
                    VdType::from_lp_csv_expr(&args[1], db),
                )
                .into()
            }
            "base_binary_opr" => {
                assert_eq!(
                    args.len(),
                    3,
                    "exprs[0].position_range = {}",
                    exprs[0].position_range
                );
                VdBaseBinaryOprSignature::new(
                    instantiation,
                    VdType::from_lp_csv_expr(&args[0], db),
                    VdType::from_lp_csv_expr(&args[1], db),
                    VdType::from_lp_csv_expr(&args[2], db),
                )
                .into()
            }
            "base_folding" => {
                assert_eq!(args.len(), 2);
                VdBaseSeparatorSignature::new(
                    instantiation,
                    VdType::from_lp_csv_expr(&args[0], db),
                    VdType::from_lp_csv_expr(&args[1], db),
                )
                .into()
            }
            "base_chaining" => {
                assert_eq!(args.len(), 2);
                VdBaseSeparatorSignature::new(
                    instantiation,
                    VdType::from_lp_csv_expr(&args[0], db),
                    VdType::from_lp_csv_expr(&args[1], db),
                )
                .into()
            }
            "base_sqrt" => {
                assert_eq!(args.len(), 2);
                VdBaseSqrtSignature::new(
                    instantiation,
                    VdType::from_lp_csv_expr(&args[0], db),
                    VdType::from_lp_csv_expr(&args[1], db),
                )
                .into()
            }
            "power" => {
                assert_eq!(args.len(), 3);
                VdPowerSignature::new(
                    instantiation,
                    VdType::from_lp_csv_expr(&args[0], db),
                    VdType::from_lp_csv_expr(&args[1], db),
                    VdType::from_lp_csv_expr(&args[2], db),
                )
                .into()
            }
            "in_set" => {
                assert_eq!(args.len(), 0);
                VdBaseContainmentSeparatorSignature::new_in_set(instantiation).into()
            }
            s => todo!("s = {s:?} not handled"),
        }
    }
}
