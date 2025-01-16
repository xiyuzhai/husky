use super::*;
use visored_global_dispatch::dispatch::separator::VdSeparatorGlobalDispatch;
use visored_mir_opr::separator::chaining::VdMirBaseComparisonSeparator;
use visored_opr::separator::VdBaseSeparator;
use visored_signature::signature::separator::base::{
    chaining::{
        relation::comparison::VdBaseComparisonSeparatorSignature, VdBaseChainingSeparatorSignature,
    },
    folding::VdBaseFoldingSeparatorSignature,
    VdBaseSeparatorSignature,
};
use visored_term::ty::VdType;

impl<'a> VdMirExprRegionDataRef<'a> {
    pub fn infer_eq_signature(
        &self,
        prev_item_ty: VdType,
        next_item_ty: VdType,
    ) -> VdBaseChainingSeparatorSignature {
        self.infer_base_chaining_separator_signature(
            prev_item_ty,
            VdBaseSeparator::Eq,
            next_item_ty,
        )
    }

    pub fn infer_add_signature(
        &self,
        prev_item_ty: VdType,
        next_item_ty: VdType,
    ) -> VdBaseFoldingSeparatorSignature {
        self.infer_base_folding_separator_signature(
            prev_item_ty,
            VdBaseSeparator::Add,
            next_item_ty,
        )
    }

    pub fn infer_mul_signature(
        &self,
        prev_item_ty: VdType,
        next_item_ty: VdType,
    ) -> VdBaseFoldingSeparatorSignature {
        self.infer_base_folding_separator_signature(
            prev_item_ty,
            VdBaseSeparator::Mul,
            next_item_ty,
        )
    }

    pub fn infer_base_chaining_separator_signature(
        &self,
        prev_item_ty: VdType,
        base_separator: VdBaseSeparator,
        next_item_ty: VdType,
    ) -> VdBaseChainingSeparatorSignature {
        match self
            .default_global_dispatch_table
            .base_separator_default_dispatch(prev_item_ty, VdBaseSeparator::Add, next_item_ty)
        {
            Some(dispatch) => match dispatch {
                VdSeparatorGlobalDispatch::Folding {
                    base_separator,
                    signature,
                } => unreachable!(),
                VdSeparatorGlobalDispatch::Chaining {
                    base_separator,
                    signature,
                } => signature,
                VdSeparatorGlobalDispatch::InSet { expr_ty } => todo!(),
            },
            None => todo!(),
        }
    }

    pub fn infer_base_folding_separator_signature(
        &self,
        prev_item_ty: VdType,
        base_separator: VdBaseSeparator,
        next_item_ty: VdType,
    ) -> VdBaseFoldingSeparatorSignature {
        match self
            .default_global_dispatch_table
            .base_separator_default_dispatch(prev_item_ty, VdBaseSeparator::Add, next_item_ty)
        {
            Some(dispatch) => match dispatch {
                VdSeparatorGlobalDispatch::Folding {
                    base_separator,
                    signature,
                } => signature,
                VdSeparatorGlobalDispatch::Chaining {
                    base_separator,
                    signature,
                } => todo!(),
                VdSeparatorGlobalDispatch::InSet { expr_ty } => todo!(),
            },
            None => todo!(),
        }
    }

    pub fn infer_base_comparison_separator_signature(
        &self,
        prev_item_ty: VdType,
        base_separator: VdMirBaseComparisonSeparator,
        next_item_ty: VdType,
    ) -> VdBaseComparisonSeparatorSignature {
        todo!()
    }
}
