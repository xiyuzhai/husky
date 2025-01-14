use super::*;
use visored_mir_expr::{
    derivation::{construction::VdMirDerivationConstruction, VdMirDerivationIdxRange},
    hypothesis::constructor::VdMirHypothesisConstructor,
};

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub fn transcribe_term_derivation(
        &self,
        src: VdBsqHypothesisIdx<'sess>,
        dst: VdBsqHypothesisIdx<'sess>,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirDerivationIdxRange {
        // TODO: Implement this
        hypothesis_constructor.alloc_derivations(vec![])
    }
}
