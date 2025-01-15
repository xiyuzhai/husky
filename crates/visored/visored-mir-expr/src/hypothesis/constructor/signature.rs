use super::*;
use visored_global_dispatch::dispatch::separator::VdSeparatorGlobalDispatch;
use visored_opr::separator::VdBaseSeparator;
use visored_signature::signature::separator::base::VdBaseSeparatorSignature;

impl<'db, Src> VdMirHypothesisConstructor<'db, Src> {
    pub fn infer_eq_signature(
        &self,
        prev_item_ty: VdType,
        next_item_ty: VdType,
    ) -> VdBaseSeparatorSignature {
        self.infer_base_separator_signature(prev_item_ty, VdBaseSeparator::Eq, next_item_ty)
    }

    pub fn infer_add_signature(
        &self,
        prev_item_ty: VdType,
        next_item_ty: VdType,
    ) -> VdBaseSeparatorSignature {
        self.infer_base_separator_signature(prev_item_ty, VdBaseSeparator::Add, next_item_ty)
    }

    pub fn infer_mul_signature(
        &self,
        prev_item_ty: VdType,
        next_item_ty: VdType,
    ) -> VdBaseSeparatorSignature {
        self.infer_base_separator_signature(prev_item_ty, VdBaseSeparator::Mul, next_item_ty)
    }

    pub fn infer_base_separator_signature(
        &self,
        prev_item_ty: VdType,
        base_separator: VdBaseSeparator,
        next_item_ty: VdType,
    ) -> VdBaseSeparatorSignature {
        match self
            .default_global_dispatch_table()
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
}
