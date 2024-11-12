use super::TranspileToLean;
use crate::{builder::VdLeanTranspilationBuilder, dictionary::item_path::VdItemPathTranslation};
use lean_hir_expr::expr::{LnHirExprData, LnHirExprIdx};
use lean_opr::opr::binary::LnBinaryOpr;
use lean_term::term::literal::{LnLiteral, LnLiteralData};
use visored_hir_expr::expr::{application::VdHirApplicationFunction, VdHirExprData, VdHirExprIdx};
use visored_zfc_ty::term::literal::{VdZfcLiteral, VdZfcLiteralData};

impl TranspileToLean<LnHirExprIdx> for VdHirExprIdx {
    fn to_lean(self, builder: &mut VdLeanTranspilationBuilder) -> LnHirExprIdx {
        let data = builder.build_expr(self);
        builder.alloc_expr(data)
    }
}

impl<'db> VdLeanTranspilationBuilder<'db> {
    pub(crate) fn build_expr(&mut self, expr: VdHirExprIdx) -> LnHirExprData {
        let db = self.db();
        match self.expr_arena()[expr] {
            VdHirExprData::Literal(literal) => LnHirExprData::Literal(to_lean_literal(db, literal)),
            VdHirExprData::ItemPath(item_path) => {
                let Some(translation) = self.dictionary().item_path_translation(item_path) else {
                    todo!()
                };
                match *translation {
                    VdItemPathTranslation::ItemPath(item_path) => {
                        LnHirExprData::ItemPath(item_path)
                    }
                }
            }
            VdHirExprData::Variable(ref vd_hir_variable) => todo!(),
            VdHirExprData::Application {
                function,
                arguments,
            } => match function {
                VdHirApplicationFunction::IntAdd => {
                    debug_assert_eq!(arguments.len(), 2);
                    let lopd = arguments.start();
                    let ropd = lopd + 1;
                    LnHirExprData::Binary {
                        lopd: lopd.to_lean(self),
                        opr: LnBinaryOpr::Add,
                        ropd: ropd.to_lean(self),
                    }
                }
                VdHirApplicationFunction::TrivialEq => {
                    debug_assert_eq!(arguments.len(), 2);
                    let lopd = arguments.start();
                    let ropd = lopd + 1;
                    LnHirExprData::Binary {
                        lopd: lopd.to_lean(self),
                        opr: LnBinaryOpr::Eq,
                        ropd: ropd.to_lean(self),
                    }
                }
            },
        }
    }
}

#[salsa::tracked]
fn to_lean_literal(db: &salsa::Db, literal: VdZfcLiteral) -> LnLiteral {
    let data = match literal.data(db) {
        VdZfcLiteralData::NaturalNumber(lit) => LnLiteralData::Nat(lit.to_string()),
        VdZfcLiteralData::NegativeInteger(_) => todo!(),
        VdZfcLiteralData::FiniteDecimalRepresentation(_) => {
            todo!()
        }
        VdZfcLiteralData::SpecialConstant(vd_zfc_special_constant) => todo!(),
    };
    LnLiteral::new(data, db)
}
