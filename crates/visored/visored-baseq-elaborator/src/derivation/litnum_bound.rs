use super::*;
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
            let prop = self.hc.arena()[dst].expr().transcribe(None, self, hc);
            hc.alloc_derivation(prop, VdMirLitnumBoundDerivationConstruction::Finish.into())
        })
    }
}
