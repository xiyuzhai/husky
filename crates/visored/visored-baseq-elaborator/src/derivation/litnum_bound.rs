use crate::term::litnum::VdBsqLitnumTerm;

use super::*;
use expr::VdBsqExpr;
use hypothesis::stashes::litnum_bound::{VdBsqLitnumBound, VdBsqLitnumBoundSrc};
use visored_mir_expr::{
    derivation::{
        chunk::VdMirDerivationChunk,
        construction::litnum_bound::VdMirLitnumBoundDerivationConstruction,
    },
    hypothesis::constructor::VdMirHypothesisConstructor,
};

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess>
where
    'db: 'sess,
{
    pub fn transcribe_litnum_bound_derivation(
        &mut self,
        dst: VdBsqHypothesisIdx<'sess>,
        bound: VdBsqLitnumBound<'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirDerivationChunk {
        hc.obtain_derivation_chunk_within_hypothesis(|hc| {
            let prop = self.hc.arena()[dst].prop().transcribe(None, self, hc);
            let src = bound.src();
            let src_nf = nf(
                src.litnum_factor(),
                src.litnum_summand(),
                src.hypothesis(),
                self,
                hc,
            );
            let dst_nf = nf(bound.litnum_factor(), bound.litnum_summand(), dst, self, hc);
            let src_nf_and_dst_nf_equivalence =
                self.transcribe_non_trivial_expr_equivalence_term_derivation(src_nf, dst_nf, hc);
            hc.alloc_derivation(
                prop,
                VdMirLitnumBoundDerivationConstruction::Finish {
                    src_nf_and_dst_nf_equivalence,
                }
                .into(),
            )
        })
    }
}

fn nf<'db, 'sess>(
    litnum_factor: VdBsqLitnumTerm<'sess>,
    litnum_summand: VdBsqLitnumTerm<'sess>,
    hypothesis: VdBsqHypothesisIdx<'sess>,
    elr: &VdBsqElaboratorInner<'db, 'sess>,
    hc: &VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdBsqExpr<'sess> {
    let litnum_factor = elr.mk_litnum(litnum_factor);
    let prop = elr.hc.arena()[hypothesis].prop();
    let (lhs, signature, rhs) = prop.split_trivial_chaining_separated_list(elr, hc);
    let expr = elr.mk_sub(lhs, rhs, hc);
    let expr = elr.mk_div(expr, litnum_factor, hc);
    let litnum_summand = elr.mk_litnum(litnum_summand);
    elr.mk_sub(expr, litnum_summand, hc)
}
