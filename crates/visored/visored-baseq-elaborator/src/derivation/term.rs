use super::*;
use expr::{VdBsqExprFld, VdBsqExprFldData};
use visored_mir_expr::{
    derivation::{
        chunk::VdMirDerivationChunk,
        construction::{term::VdMirTermDerivationConstruction, VdMirDerivationConstruction},
        VdMirDerivationIdx, VdMirDerivationIdxRange,
    },
    expr::VdMirExprIdx,
    hypothesis::{constructor::VdMirHypothesisConstructor, VdMirHypothesisIdx},
};

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess>
where
    'db: 'sess,
{
    pub fn transcribe_term_derivation(
        &self,
        src: VdBsqHypothesisIdx<'sess>,
        dst: VdBsqHypothesisIdx<'sess>,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirDerivationChunk {
        hypothesis_constructor.obtain_derivation_chunk_within_hypothesis(|hypothesis_constructor| {
            let src_term_equivalent = self.transcribe_expr_term_derivation(
                self.hypothesis_constructor.arena()[src].expr(),
                hypothesis_constructor,
            );
            let dst_term_equivalent = self.transcribe_expr_term_derivation(
                self.hypothesis_constructor.arena()[dst].expr(),
                hypothesis_constructor,
            );
            let prop = self.hypothesis_constructor.arena()[dst].expr();
            let prop = self.transcribe_expr(prop, hypothesis_constructor);
            hypothesis_constructor.alloc_derivation(
                prop,
                VdMirDerivationConstruction::Term(VdMirTermDerivationConstruction::Finalize {
                    src_term_equivalent,
                    dst_term_equivalent,
                }),
            )
        })
    }

    fn transcribe_expr_term_derivation(
        &self,
        expr: VdBsqExprFld<'sess>,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirDerivationIdx {
        let (expr, construction) =
            self.transcribe_expr_term_derivation_inner(expr, hypothesis_constructor);
        hypothesis_constructor.alloc_derivation(expr, construction)
    }

    fn transcribe_expr_term_derivation_inner(
        &self,
        expr: VdBsqExprFld<'sess>,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> (VdMirExprIdx, VdMirDerivationConstruction) {
        match expr.data() {
            VdBsqExprFldData::Literal(vd_literal) => todo!(),
            VdBsqExprFldData::Variable(lx_math_letter, arena_idx) => todo!(),
            VdBsqExprFldData::Application {
                function,
                arguments,
            } => todo!(),
            VdBsqExprFldData::FoldingSeparatedList { leader, followers } => todo!(),
            VdBsqExprFldData::ChainingSeparatedList {
                leader,
                followers,
                joined_signature,
            } => todo!(),
            VdBsqExprFldData::ItemPath(vd_item_path) => todo!(),
        }
    }
}
