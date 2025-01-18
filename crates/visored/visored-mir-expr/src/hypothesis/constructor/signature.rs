use super::*;
use visored_global_dispatch::dispatch::{
    attach::VdAttachGlobalDispatch, binary_opr::VdBinaryOprGlobalDispatch,
    prefix_opr::VdPrefixOprGlobalDispatch, separator::VdSeparatorGlobalDispatch,
    sqrt::VdSqrtGlobalDispatch,
};
use visored_mir_opr::separator::chaining::VdMirBaseComparisonSeparator;
use visored_opr::{
    opr::{binary::VdBaseBinaryOpr, prefix::VdBasePrefixOpr},
    separator::VdBaseSeparator,
};
use visored_signature::signature::{
    attach::{VdAttachSignature, VdPowerSignature},
    binary_opr::base::VdBaseBinaryOprSignature,
    prefix_opr::VdBasePrefixOprSignature,
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
    pub fn infer_equivalence_signature(
        &self,
        prev_item_ty: VdType,
        next_item_ty: VdType,
    ) -> VdBaseChainingSeparatorSignature {
        let separator = if prev_item_ty == self.ty_menu.prop {
            VdBaseSeparator::Leftrightarrow
        } else {
            VdBaseSeparator::Eq
        };
        self.infer_base_chaining_separator_signature(prev_item_ty, separator, next_item_ty)
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

    pub fn infer_sub_signature(
        &self,
        prev_item_ty: VdType,
        next_item_ty: VdType,
    ) -> VdBaseBinaryOprSignature {
        self.infer_base_binary_opr_signature(prev_item_ty, VdBaseBinaryOpr::Sub, next_item_ty)
    }

    pub fn infer_neg_signature(&self, item_ty: VdType) -> VdBasePrefixOprSignature {
        self.infer_base_prefix_opr_signature(item_ty, VdBasePrefixOpr::Neg)
    }

    pub fn infer_base_prefix_opr_signature(
        &self,
        opd_ty: VdType,
        opr: VdBasePrefixOpr,
    ) -> VdBasePrefixOprSignature {
        match self
            .default_global_dispatch_table
            .base_prefix_opr_default_dispatch(opr, opd_ty)
            .unwrap()
        {
            VdPrefixOprGlobalDispatch::Base { signature, .. } => signature,
        }
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

    pub fn infer_base_binary_opr_signature(
        &self,
        lopd_ty: VdType,
        opr: VdBaseBinaryOpr,
        ropd_ty: VdType,
    ) -> VdBaseBinaryOprSignature {
        match self
            .default_global_dispatch_table
            .base_binary_opr_default_dispatch(lopd_ty, opr, ropd_ty)
            .unwrap()
        {
            VdBinaryOprGlobalDispatch::Normal {
                base_binary_opr,
                signature,
            } => signature,
        }
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
                    VdBaseChainingSeparatorSignature::Iff { .. } => todo!(),
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
        let Some(dispatch) = self
            .default_global_dispatch_table
            .power_default_dispatch(base_ty, exponent_ty)
        else {
            todo!("base_ty: `{:?}`, exponent_ty: `{:?}`", base_ty, exponent_ty)
        };
        match dispatch {
            VdAttachGlobalDispatch::Normal { signature } => match signature {
                VdAttachSignature::Power(signature) => signature,
            },
        }
    }
}
