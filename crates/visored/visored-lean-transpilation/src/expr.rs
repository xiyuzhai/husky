pub mod application;
mod separated_list;

use super::VdTranspileToLean;
use crate::{
    builder::VdLeanTranspilationBuilder,
    dictionary::{func_key::VdFuncKeyTranslation, item_path::VdItemPathTranslation},
};
use either::*;
use lean_mir_expr::expr::{application::LnMirFunc, LnMirExprData, LnMirExprIdx, LnMirExprIdxRange};
use lean_opr::opr::binary::LnBinaryOpr;
use lean_term::term::literal::{LnLiteral, LnLiteralData};
use visored_mir_expr::expr::{
    application::VdMirFunc, VdMirExprData, VdMirExprIdx, VdMirExprIdxRange,
};
use visored_term::term::literal::{VdLiteral, VdLiteralData};

impl VdTranspileToLean<LnMirExprIdx> for VdMirExprIdx {
    fn to_lean(self, builder: &mut VdLeanTranspilationBuilder) -> LnMirExprIdx {
        let data = builder.build_expr(self);
        builder.alloc_expr(data)
    }
}

impl<'db, I> VdTranspileToLean<LnMirExprIdxRange> for I
where
    I: Copy + IntoIterator<Item = VdMirExprIdx>,
{
    fn to_lean(self, builder: &mut VdLeanTranspilationBuilder) -> LnMirExprIdxRange {
        let mut exprs = vec![];
        for expr in self {
            exprs.push(builder.build_expr(expr));
        }
        builder.alloc_exprs(exprs)
    }
}

impl<'db> VdLeanTranspilationBuilder<'db> {
    pub(crate) fn build_expr(&mut self, expr: VdMirExprIdx) -> LnMirExprData {
        match self.expr_arena()[expr] {
            VdMirExprData::Literal(literal) => LnMirExprData::Literal(*to_lean_literal(literal)),
            VdMirExprData::ItemPath(item_path) => {
                let Some(translation) = self.dictionary().item_path_translation(item_path) else {
                    todo!()
                };
                match *translation {
                    VdItemPathTranslation::ItemPath(item_path) => {
                        LnMirExprData::ItemPath(item_path)
                    }
                }
            }
            // TODO: consider variable deps
            VdMirExprData::Variable(local_defn) => LnMirExprData::Variable {
                ident: self.mangle_symbol(local_defn),
            },
            VdMirExprData::Application {
                function,
                arguments,
            } => self.build_application(expr, function, arguments),
            VdMirExprData::FoldingSeparatedList {
                leader,
                ref followers,
            } => self.build_folding_separated_list(leader, followers),
            VdMirExprData::ChainingSeparatedList {
                leader,
                ref followers,
                joined_separator_and_signature,
            } => self.build_chaining_separated_list(
                leader,
                followers,
                joined_separator_and_signature,
            ),
        }
    }
}

#[interned::memo]
fn to_lean_literal(literal: VdLiteral) -> LnLiteral {
    let data = match literal.data() {
        VdLiteralData::NaturalNumber(lit) => LnLiteralData::Nat(lit.to_string()),
        VdLiteralData::NegativeInteger(_) => todo!(),
        VdLiteralData::Float(lit) => LnLiteralData::Float(lit.to_string()),
        VdLiteralData::SpecialConstant(vd_special_constant) => todo!(),
    };
    LnLiteral::new(data)
}

impl<'db> VdTranspileToLean<LnMirFunc> for VdMirFunc {
    fn to_lean(self, builder: &mut VdLeanTranspilationBuilder) -> LnMirFunc {
        match self.key_or_expr() {
            Left(key) => {
                let Some(translation) = builder.dictionary().func_key_translation(key) else {
                    todo!()
                };
                match *translation {
                    VdFuncKeyTranslation::PrefixOpr(func_key)
                    | VdFuncKeyTranslation::FoldingBinaryOpr(func_key)
                    | VdFuncKeyTranslation::ChainingBinaryOpr(func_key)
                    | VdFuncKeyTranslation::Power(func_key)
                    | VdFuncKeyTranslation::Function(func_key)
                    | VdFuncKeyTranslation::JustBinaryOpr(func_key) => {
                        builder.build_func_from_key(func_key)
                    }
                    VdFuncKeyTranslation::InSet => LnMirFunc::InSet,
                }
            }
            Right(_) => todo!(),
        }
    }
}
