pub mod application;

use super::VdTranspileToLean;
use crate::{builder::VdLeanTranspilationBuilder, dictionary::item_path::VdItemPathTranslation};
use lean_mir_expr::expr::{LnMirExprData, LnMirExprIdx, LnMirExprIdxRange};
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

impl<'db> VdTranspileToLean<LnMirExprIdxRange> for VdMirExprIdxRange {
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
        let db = self.db();
        match self.expr_arena()[expr] {
            VdMirExprData::Literal(literal) => LnMirExprData::Literal(to_lean_literal(db, literal)),
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
        }
    }
}

#[salsa::tracked]
fn to_lean_literal(db: &salsa::Db, literal: VdLiteral) -> LnLiteral {
    let data = match literal.data(db) {
        VdLiteralData::NaturalNumber(lit) => LnLiteralData::Nat(lit.to_string()),
        VdLiteralData::NegativeInteger(_) => todo!(),
        VdLiteralData::FiniteDecimalRepresentation(_) => {
            todo!()
        }
        VdLiteralData::SpecialConstant(vd_special_constant) => todo!(),
    };
    LnLiteral::new(data, db)
}
