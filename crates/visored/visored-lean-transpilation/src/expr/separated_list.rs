use super::*;
use crate::dictionary::func_key::VdFuncKeyTranslation;
use either::*;
use lean_mir_expr::expr::application::{LnMirFunc, LnMirFuncKey};
use smallvec::*;
use visored_mir_expr::expr::VdMirExprIdxRange;
use visored_mir_opr::separator::VdMirBaseSeparator;
use visored_signature::signature::separator::base::{
    chaining::VdBaseChainingSeparatorSignature, folding::VdBaseFoldingSeparatorSignature,
    VdBaseSeparatorSignature,
};

impl<'db, S> VdLeanTranspilationBuilder<'db, S>
where
    S: IsVdLeanTranspilationScheme,
{
    pub(super) fn build_folding_separated_list(
        &mut self,
        leader: VdMirExprIdx,
        followers: &[(VdBaseFoldingSeparatorSignature, VdMirExprIdx)],
    ) -> LnMirExprData {
        debug_assert!(followers.len() >= 1);
        let mut follower_iter = followers.iter().copied();
        let mut result = self.build_expr_data(leader);
        let mut result_ty = self.expr_arena()[leader].ty();
        for (signature, follower) in follower_iter {
            let follower = self.build_expr_entry(follower);
            let function = self.build_folding_func(signature);
            let result_expected_ty = signature.item_ty();
            let result_ty_ascription = match result_expected_ty.to_lean(self) {
                VdTypeLeanTranspilation::Type(expected_ty) => expected_ty,
            };
            result = LnMirExprData::Application {
                function,
                arguments: self.alloc_exprs([LnMirExprEntry::new(result), follower]),
            };
            result = LnMirExprData::TypeAscription {
                expr: self.alloc_expr(LnMirExprEntry::new(result)),
                ty_ascription: result_ty_ascription,
            };
            result_ty = signature.expr_ty();
        }
        result
    }

    fn build_folding_func(&mut self, signature: VdBaseFoldingSeparatorSignature) -> LnMirFunc {
        let Some(translation) = self.dictionary().func_key_translation(signature.into()) else {
            todo!("no translation for func key `{:?}`", signature)
        };
        let VdFuncKeyTranslation::FoldingBinaryOpr(func_key) = *translation else {
            todo!()
        };
        self.build_func_from_key(func_key)
    }

    pub(super) fn build_chaining_separated_list(
        &mut self,
        leader: VdMirExprIdx,
        followers: &[(VdBaseChainingSeparatorSignature, VdMirExprIdx)],
        joined_signature: Option<VdBaseChainingSeparatorSignature>,
    ) -> LnMirExprData {
        if followers.len() != 1 {
            todo!()
        }
        let leader = self.build_expr_entry(leader);
        let (func, follower) = *followers.first().unwrap();
        let follower = self.build_expr_entry(follower);
        LnMirExprData::Application {
            function: func.to_lean(self),
            arguments: self.alloc_exprs([leader, follower]),
        }
    }
}
