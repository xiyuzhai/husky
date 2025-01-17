use super::*;
use visored_global_dispatch::dispatch::{
    attach::VdAttachGlobalDispatch, separator::VdSeparatorGlobalDispatch,
    sqrt::VdSqrtGlobalDispatch,
};
use visored_mir_opr::separator::chaining::VdMirBaseComparisonSeparator;
use visored_opr::separator::VdBaseSeparator;
use visored_signature::signature::{
    attach::{VdAttachSignature, VdPowerSignature},
    separator::base::{
        chaining::{
            relation::{
                comparison::VdBaseComparisonSeparatorSignature, VdBaseRelationSeparatorSignature,
            },
            VdBaseChainingSeparatorSignature,
        },
        folding::VdBaseFoldingSeparatorSignature,
        VdBaseSeparatorSignature,
    },
    sqrt::VdBaseSqrtSignature,
};

impl<'db, Src> VdMirHypothesisConstructor<'db, Src> {
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
            VdBaseSeparator::Times,
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
            .default_global_dispatch_table()
            .base_separator_default_dispatch(prev_item_ty, base_separator, next_item_ty)
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
            .default_global_dispatch_table()
            .base_separator_default_dispatch(prev_item_ty, base_separator, next_item_ty)
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
            },
            None => todo!(
                "prev_item_ty: `{:?}`, base_separator: `{:?}`, next_item_ty: `{:?}`",
                prev_item_ty,
                base_separator,
                next_item_ty
            ),
        }
    }

    pub fn infer_base_comparison_separator_signature(
        &self,
        prev_item_ty: VdType,
        base_separator: VdMirBaseComparisonSeparator,
        next_item_ty: VdType,
    ) -> VdBaseComparisonSeparatorSignature {
        match self
            .default_global_dispatch_table()
            .base_separator_default_dispatch(prev_item_ty, base_separator.into(), next_item_ty)
        {
            Some(dispatch) => match dispatch {
                VdSeparatorGlobalDispatch::Folding {
                    base_separator,
                    signature,
                } => todo!(),
                VdSeparatorGlobalDispatch::Chaining {
                    base_separator,
                    signature,
                } => match signature {
                    VdBaseChainingSeparatorSignature::Iff => todo!(),
                    VdBaseChainingSeparatorSignature::Relation(signature) => match signature {
                        VdBaseRelationSeparatorSignature::Containment(signature) => todo!(),
                        VdBaseRelationSeparatorSignature::Comparison(signature) => signature,
                    },
                },
            },
            None => todo!(),
        }
    }

    pub fn infer_base_sqrt_signature(&self, radicand_ty: VdType) -> VdBaseSqrtSignature {
        match self
            .default_global_dispatch_table
            .base_sqrt_default_dispatch(radicand_ty)
            .unwrap()
        {
            VdSqrtGlobalDispatch::Base { signature } => signature,
        }
    }

    pub fn infer_power_signature(&self, base_ty: VdType, exponent_ty: VdType) -> VdPowerSignature {
        match self
            .default_global_dispatch_table
            .power_default_dispatch(base_ty, exponent_ty)
            .unwrap()
        {
            VdAttachGlobalDispatch::Normal { signature } => match signature {
                VdAttachSignature::Power(signature) => signature,
            },
        }
    }
}
