use super::*;
use expr::{VdBsqExprFld, VdBsqExprFldData};
use smallvec::*;
use visored_mir_expr::{
    derivation::{
        chunk::VdMirDerivationChunk,
        construction::{term::VdMirTermDerivationConstruction, VdMirDerivationConstruction},
        VdMirDerivationIdx, VdMirDerivationIdxRange,
    },
    expr::{application::VdMirFunc, VdMirExprData, VdMirExprEntry, VdMirExprIdx},
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
            let src_term_equivalence = self.transcribe_expr_term_derivation(
                self.hypothesis_constructor.arena()[src].expr(),
                hypothesis_constructor,
            );
            let dst_term_equivalence = self.transcribe_expr_term_derivation(
                self.hypothesis_constructor.arena()[dst].expr(),
                hypothesis_constructor,
            );
            let prop = self.hypothesis_constructor.arena()[dst].expr();
            let prop = self.transcribe_expr(prop, hypothesis_constructor);
            hypothesis_constructor.alloc_derivation(
                prop,
                VdMirDerivationConstruction::Term(VdMirTermDerivationConstruction::Finalize {
                    src_term_equivalence,
                    dst_term_equivalence,
                }),
            )
        })
    }

    fn transcribe_expr_term_derivation(
        &self,
        expr: VdBsqExprFld<'sess>,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirDerivationIdx {
        let prop = self.transcribe_expr_term_derivation_prop(expr, hypothesis_constructor);
        let construction =
            self.transcribe_expr_term_derivation_construction(expr, hypothesis_constructor);
        hypothesis_constructor.alloc_derivation(prop, construction.into())
    }

    fn transcribe_expr_term_derivation_prop(
        &self,
        expr: VdBsqExprFld<'sess>,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirExprIdx {
        let term = expr.term();
        let expr_transcription = self.transcribe_expr(expr, hypothesis_constructor);
        let term_transcription =
            self.transcribe_term(term, expr.expected_ty(), hypothesis_constructor);
        let eq_func = VdMirFunc::NormalBaseSeparator(self.eq_signature(expr.ty()));
        let prop_expr_data = VdMirExprData::ChainingSeparatedList {
            leader: expr_transcription,
            followers: smallvec![(eq_func, term_transcription)],
            joined_signature: None,
        };
        let prop_expr_ty = self.ty_menu().prop;
        hypothesis_constructor.construct_expr(VdMirExprEntry::new(
            prop_expr_data,
            prop_expr_ty,
            None,
        ))
    }

    fn transcribe_expr_term_derivation_construction(
        &self,
        expr: VdBsqExprFld<'sess>,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirTermDerivationConstruction {
        match expr.data() {
            VdBsqExprFldData::Literal(_)
            | VdBsqExprFldData::Variable(_, _)
            | VdBsqExprFldData::ItemPath(_) => VdMirTermDerivationConstruction::Obvious,
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
        }
    }
}
