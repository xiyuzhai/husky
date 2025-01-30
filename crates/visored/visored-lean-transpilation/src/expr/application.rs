use super::*;
use crate::dictionary::func_key::VdFuncKeyTranslation;
use either::*;
use lean_mir_expr::expr::application::LnMirFuncKey;
use lean_opr::opr::prefix::LnPrefixOpr;
use smallvec::*;
use visored_mir_expr::expr::{VdMirExprEntry, VdMirExprIdxRange};

impl<'db, S> VdLeanTranspilationBuilder<'db, S>
where
    S: IsVdLeanTranspilationScheme,
{
    pub(super) fn build_application(
        &mut self,
        expr: VdMirExprIdx,
        func: VdMirFunc,
        arguments: VdMirExprIdxRange,
    ) -> LnMirExprData {
        match func.key_or_expr() {
            Left(func_key) => {
                let Some(translation) = self.dictionary().func_key_translation(func_key) else {
                    todo!("no translation for func key `{:?}`", func_key)
                };
                match *translation {
                    VdFuncKeyTranslation::PrefixOpr(func_key) => match func_key {
                        LnMirFuncKey::PrefixOpr { opr, instantiation } => {
                            let ty = self.expr_arena()[expr].ty();
                            match ty.to_lean(self) {
                                VdTypeLeanTranspilation::Type(ty_ascription) => {
                                    let data = LnMirExprData::Application {
                                        function: self.build_func_from_key(func_key),
                                        arguments: arguments.to_lean(self),
                                    };
                                    LnMirExprData::TypeAscription {
                                        expr: self.alloc_expr(LnMirExprEntry::new(data)),
                                        ty_ascription,
                                    }
                                }
                            }
                        }
                        _ => unreachable!(),
                    },
                    VdFuncKeyTranslation::FoldingBinaryOpr(func_key) => {
                        todo!()
                        // self.build_folding_separated_list(expr, func_key, arguments)
                    }
                    // TODO: implement
                    VdFuncKeyTranslation::InSet => LnMirExprData::Sorry,
                    VdFuncKeyTranslation::Power(func_key) => LnMirExprData::Application {
                        function: self.build_func_from_key(func_key),
                        arguments: arguments.to_lean(self),
                    },
                    VdFuncKeyTranslation::ChainingBinaryOpr(func_key) => {
                        todo!()
                        // self.build_chaining_separated_list(expr, func_key, arguments)
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
}
