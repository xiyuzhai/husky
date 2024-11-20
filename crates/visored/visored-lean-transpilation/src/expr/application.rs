use super::*;
use crate::dictionary::func_key::VdFuncKeyTranslation;
use either::*;
use lean_mir_expr::expr::application::LnMirFuncKey;
use smallvec::*;
use visored_mir_expr::expr::VdMirExprIdxRange;

impl<'db> VdLeanTranspilationBuilder<'db> {
    pub(super) fn build_application(
        &mut self,
        expr: VdMirExprIdx,
        func: VdMirFunc,
        arguments: VdMirExprIdxRange,
    ) -> LnMirExprData {
        match func.key_or_expr(self.db()) {
            Left(func_key) => {
                let Some(translation) = self.dictionary().func_key_translation(func_key) else {
                    use salsa::DebugWithDb;
                    todo!(
                        "no translation for func key `{:?}`",
                        func_key.debug(self.db())
                    )
                };
                match *translation {
                    VdFuncKeyTranslation::PrefixOpr(func_key) => LnMirExprData::Application {
                        function: self.build_func_from_key(func_key),
                        arguments: arguments.to_lean(self),
                    },
                    VdFuncKeyTranslation::FoldingBinaryOpr(func_key) => {
                        self.build_folding_separated_list(expr, func_key, arguments)
                    }
                    // TODO: implement
                    VdFuncKeyTranslation::InSet => LnMirExprData::Sorry,
                    VdFuncKeyTranslation::Power(func_key) => LnMirExprData::Application {
                        function: self.build_func_from_key(func_key),
                        arguments: arguments.to_lean(self),
                    },
                    VdFuncKeyTranslation::ChainingBinaryOpr(func_key) => {
                        self.build_chaining_separated_list(expr, func_key, arguments)
                    }
                    VdFuncKeyTranslation::Function(func_key) => LnMirExprData::Application {
                        function: self.build_func_from_key(func_key),
                        arguments: arguments.to_lean(self),
                    },
                    VdFuncKeyTranslation::JustBinaryOpr(func_key) => LnMirExprData::Application {
                        function: self.build_func_from_key(func_key),
                        arguments: arguments.to_lean(self),
                    },
                }
            }
            Right(_) => todo!(),
        }
    }

    fn build_folding_separated_list(
        &mut self,
        expr: VdMirExprIdx,
        func_key: LnMirFuncKey,
        arguments: VdMirExprIdxRange,
    ) -> LnMirExprData {
        debug_assert!(arguments.len() >= 2);
        let mut argument_iter = arguments.into_iter();
        let fst = self.build_expr(argument_iter.next().unwrap());
        let snd = self.build_expr(argument_iter.next().unwrap());
        let mut result = LnMirExprData::Application {
            function: self.build_func_from_key(func_key),
            arguments: self.alloc_exprs([fst, snd]),
        };
        for argument in argument_iter {
            let argument = self.build_expr(argument);
            result = LnMirExprData::Application {
                function: self.build_func_from_key(func_key),
                arguments: self.alloc_exprs([result, argument]),
            };
        }
        result
    }

    fn build_chaining_separated_list(
        &mut self,
        expr: VdMirExprIdx,
        func_key: LnMirFuncKey,
        arguments: VdMirExprIdxRange,
    ) -> LnMirExprData {
        if arguments.len() != 2 {
            todo!()
        }
        let fst = self.build_expr(arguments.first().unwrap());
        let snd = self.build_expr(arguments.last().unwrap());
        LnMirExprData::Application {
            function: self.build_func_from_key(func_key),
            arguments: self.alloc_exprs([fst, snd]),
        }
    }
}
