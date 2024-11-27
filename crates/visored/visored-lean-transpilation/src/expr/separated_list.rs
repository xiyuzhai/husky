use super::*;
use crate::dictionary::func_key::VdFuncKeyTranslation;
use either::*;
use lean_mir_expr::expr::application::{LnMirFunc, LnMirFuncKey};
use smallvec::*;
use visored_mir_expr::expr::VdMirExprIdxRange;
use visored_opr::{opr::binary::VdBaseBinaryOpr, separator::VdBaseSeparator};
use visored_signature::signature::separator::base::VdBaseSeparatorSignature;

impl<'db> VdLeanTranspilationBuilder<'db> {
    pub(super) fn build_folding_separated_list(
        &mut self,
        leader: VdMirExprIdx,
        followers: &[(VdMirFunc, VdMirExprIdx)],
    ) -> LnMirExprData {
        debug_assert!(followers.len() >= 1);
        let mut follower_iter = followers.iter().copied();
        let leader = self.build_expr(leader);
        let (fst_func, fst_follower) = follower_iter.next().unwrap();
        let fst_follower = self.build_expr(fst_follower);
        let mut result = LnMirExprData::Application {
            function: self.build_folding_func(fst_func),
            arguments: self.alloc_exprs([leader, fst_follower]),
        };
        for (func, follower) in follower_iter {
            let follower = self.build_expr(follower);
            let function = self.build_folding_func(func);
            result = LnMirExprData::Application {
                function,
                arguments: self.alloc_exprs([result, follower]),
            };
        }
        result
    }

    fn build_folding_func(&mut self, func: VdMirFunc) -> LnMirFunc {
        match func.key_or_expr() {
            Left(func_key) => {
                let Some(translation) = self.dictionary().func_key_translation(func_key) else {
                    todo!("no translation for func key `{:?}`", func_key)
                };
                let VdFuncKeyTranslation::FoldingBinaryOpr(func_key) = *translation else {
                    todo!()
                };
                self.build_func_from_key(func_key)
            }
            Right(_) => todo!(),
        }
    }

    pub(super) fn build_chaining_separated_list(
        &mut self,
        leader: VdMirExprIdx,
        followers: &[(VdMirFunc, VdMirExprIdx)],
        joined_separator_and_signature: Option<(VdBaseSeparator, VdBaseSeparatorSignature)>,
    ) -> LnMirExprData {
        if followers.len() != 1 {
            todo!()
        }
        let leader = self.build_expr(leader);
        let (func, follower) = *followers.first().unwrap();
        let follower = self.build_expr(follower);
        LnMirExprData::Application {
            function: func.to_lean(self),
            arguments: self.alloc_exprs([leader, follower]),
        }
    }
}
