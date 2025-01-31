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
        src: VdBsqLitnumBoundSrc<'sess>,
        bound: VdBsqLitnumBound<'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirDerivationChunk {
        hc.obtain_derivation_chunk_within_hypothesis(|hc| {
            p!(src, self.hc.arena()[src.hypothesis()], self.hc.arena()[dst]);
            let prop = todo!();
            hc.alloc_derivation(prop, VdMirLitnumBoundDerivationConstruction::Finish.into())
        })
    }
}
