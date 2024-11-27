mod lisp_csv;

use crate::dispatch::separator::join::VdBaseChainingSeparatorJoinKey;
use crate::{
    dispatch::{
        attach::VdAttachGlobalDispatch, binary_opr::VdBinaryOprGlobalDispatch,
        frac::VdFracGlobalDispatch, prefix_opr::VdPrefixOprGlobalDispatch,
        separator::VdSeparatorGlobalDispatch, sqrt::VdSqrtGlobalDispatch,
    },
    menu::vd_global_dispatch_menu,
    *,
};
use dispatch::separator::join::VdBaseChainingSeparatorJoinDispatch;
use rustc_hash::FxHashMap;
use visored_opr::{
    menu::vd_opr_menu,
    opr::{binary::VdBaseBinaryOpr, prefix::VdBasePrefixOpr},
    separator::VdBaseSeparator,
};
use visored_signature::{
    menu::vd_signature_menu, signature::separator::base::VdBaseSeparatorSignature,
    table::VdSignatureTable,
};
use visored_term::{menu::VD_TYPE_MENU, ty::VdType};

pub struct VdDefaultGlobalDispatchTable {
    base_prefix_opr_default_dispatch_table:
        FxHashMap<VdBasePrefixOprKey, VdPrefixOprGlobalDispatch>,
    base_binary_opr_default_dispatch_table:
        FxHashMap<VdBaseBinaryOprKey, VdBinaryOprGlobalDispatch>,
    base_separator_default_dispatch_table: FxHashMap<VdBaseSeparatorKey, VdSeparatorGlobalDispatch>,
    attach_default_dispatch_table: FxHashMap<VdAttachKey, VdAttachGlobalDispatch>,
    base_sqrt_default_dispatch_table: FxHashMap<VdBaseSqrtKey, VdSqrtGlobalDispatch>,
    base_frac_default_dispatch_table: FxHashMap<VdBaseFracKey, VdFracGlobalDispatch>,
    base_chaining_separator_join_dispatch_table:
        FxHashMap<VdBaseChainingSeparatorJoinKey, VdBaseChainingSeparatorJoinDispatch>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VdBaseBinaryOprKey {
    pub lopd_ty: VdType,
    pub base_binary_opr: VdBaseBinaryOpr,
    pub ropd_ty: VdType,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VdBaseSeparatorKey {
    pub base_separator: VdBaseSeparator,
    pub prev_item_ty: VdType,
    pub next_item_ty: VdType,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VdBasePrefixOprKey {
    pub base_opr: VdBasePrefixOpr,
    pub opd_ty: VdType,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VdAttachKey {
    Power {
        base_ty: VdType,
        exponent_ty: VdType,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VdBaseSqrtKey {
    pub base_ty: VdType,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VdBaseFracKey {
    pub numerator_ty: VdType,
    pub denominator_ty: VdType,
}

impl VdDefaultGlobalDispatchTable {
    pub fn new(
        base_prefix_opr_default_dispatches: impl IntoIterator<
            Item = (VdBasePrefixOprKey, VdPrefixOprGlobalDispatch),
        >,
        base_binary_opr_default_dispatches: impl IntoIterator<
            Item = (VdBaseBinaryOprKey, VdBinaryOprGlobalDispatch),
        >,
        base_separator_default_dispatches: impl IntoIterator<
            Item = (VdBaseSeparatorKey, VdSeparatorGlobalDispatch),
        >,
        attach_default_dispatches: impl IntoIterator<Item = (VdAttachKey, VdAttachGlobalDispatch)>,
        sqrt_default_dispatches: impl IntoIterator<Item = (VdBaseSqrtKey, VdSqrtGlobalDispatch)>,
        frac_default_dispatches: impl IntoIterator<Item = (VdBaseFracKey, VdFracGlobalDispatch)>,
        base_chaining_separator_join_default_dispatches: impl IntoIterator<
            Item = (
                VdBaseChainingSeparatorJoinKey,
                VdBaseChainingSeparatorJoinDispatch,
            ),
        >,
    ) -> Self {
        Self {
            base_prefix_opr_default_dispatch_table: base_prefix_opr_default_dispatches
                .into_iter()
                .collect(),
            base_binary_opr_default_dispatch_table: base_binary_opr_default_dispatches
                .into_iter()
                .collect(),
            base_separator_default_dispatch_table: base_separator_default_dispatches
                .into_iter()
                .collect(),
            attach_default_dispatch_table: attach_default_dispatches.into_iter().collect(),
            base_sqrt_default_dispatch_table: sqrt_default_dispatches.into_iter().collect(),
            base_frac_default_dispatch_table: frac_default_dispatches.into_iter().collect(),
            base_chaining_separator_join_dispatch_table:
                base_chaining_separator_join_default_dispatches
                    .into_iter()
                    .collect(),
        }
    }
}

impl VdDefaultGlobalDispatchTable {
    pub fn base_binary_opr_default_dispatch(
        &self,
        lopd_ty: VdType,
        base_binary_opr: VdBaseBinaryOpr,
        ropd_ty: VdType,
    ) -> Option<VdBinaryOprGlobalDispatch> {
        self.base_binary_opr_default_dispatch_table
            .get(&VdBaseBinaryOprKey {
                base_binary_opr,
                lopd_ty,
                ropd_ty,
            })
            .copied()
    }

    pub fn base_separator_default_dispatch(
        &self,
        prev_item_ty: VdType,
        base_separator: VdBaseSeparator,
        next_item_ty: VdType,
    ) -> Option<VdSeparatorGlobalDispatch> {
        self.base_separator_default_dispatch_table
            .get(&VdBaseSeparatorKey {
                base_separator,
                prev_item_ty,
                next_item_ty,
            })
            .copied()
    }

    pub fn base_chaining_separator_join_default_dispatch(
        &self,
        prev: VdBaseSeparatorSignature,
        next: VdBaseSeparatorSignature,
    ) -> Option<VdBaseChainingSeparatorJoinDispatch> {
        self.base_chaining_separator_join_dispatch_table
            .get(&VdBaseChainingSeparatorJoinKey { prev, next })
            .copied()
    }

    pub fn base_prefix_opr_default_dispatch(
        &self,
        base_opr: VdBasePrefixOpr,
        opd_ty: VdType,
    ) -> Option<VdPrefixOprGlobalDispatch> {
        self.base_prefix_opr_default_dispatch_table
            .get(&VdBasePrefixOprKey { base_opr, opd_ty }.into())
            .copied()
    }

    pub fn power_default_dispatch(
        &self,
        base_ty: VdType,
        exponent_ty: VdType,
    ) -> Option<VdAttachGlobalDispatch> {
        self.attach_default_dispatch_table
            .get(&VdAttachKey::Power {
                base_ty,
                exponent_ty,
            })
            .copied()
    }

    pub fn base_sqrt_default_dispatch(&self, base_ty: VdType) -> Option<VdSqrtGlobalDispatch> {
        self.base_sqrt_default_dispatch_table
            .get(&VdBaseSqrtKey { base_ty })
            .copied()
    }

    pub fn base_frac_default_dispatch(
        &self,
        numerator_ty: VdType,
        denominator_ty: VdType,
    ) -> Option<VdFracGlobalDispatch> {
        self.base_frac_default_dispatch_table
            .get(&VdBaseFracKey {
                numerator_ty,
                denominator_ty,
            })
            .copied()
    }
}

impl VdDefaultGlobalDispatchTable {
    pub fn from_standard_lisp_csv_file_dir() -> Self {
        let husky_lang_dev_paths = husky_path_utils::HuskyLangDevPaths::new();
        let specs_dir = husky_lang_dev_paths.specs_dir();
        let dir = &specs_dir.join("visored/global_default_dispatches");
        let signature_table = VdSignatureTable::from_lp_csv_file_path(
            &specs_dir.join("visored/signature_table.lpcsv"),
        );
        VdDefaultGlobalDispatchTable::from_lisp_csv_file_dir(dir, &signature_table)
    }
}
