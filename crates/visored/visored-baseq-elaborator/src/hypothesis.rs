pub mod construction;
pub mod constructor;
pub mod contradiction;
pub mod region;
pub mod stack;
pub mod stash;
pub mod stashes;

use self::construction::VdBsqHypothesisConstruction;
use crate::{elaborator::VdBsqElaboratorInner, expr::VdBsqExprFld};
use idx_arena::{Arena, ArenaIdx};
use visored_mir_expr::{
    expr::VdMirExprIdx,
    hypothesis::{
        construction::VdMirHypothesisConstruction, constructor::VdMirHypothesisConstructor,
        VdMirHypothesisIdx,
    },
};

#[derive(Debug, Eq, PartialEq)]
pub struct VdBsqHypothesisEntry<'sess> {
    prop: VdBsqExprFld<'sess>,
    construction: VdBsqHypothesisConstruction<'sess>,
}

#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub struct VdBsqHypothesisIdx<'sess>(ArenaIdx<VdBsqHypothesisEntry<'sess>>);

#[derive(Debug, Default, Eq, PartialEq)]
pub struct VdBsqHypothesisArena<'sess>(Arena<VdBsqHypothesisEntry<'sess>>);

impl<'sess> std::ops::Index<VdBsqHypothesisIdx<'sess>> for VdBsqHypothesisArena<'sess> {
    type Output = VdBsqHypothesisEntry<'sess>;

    fn index(&self, index: VdBsqHypothesisIdx<'sess>) -> &Self::Output {
        &self.0[index.0]
    }
}

impl<'sess> std::ops::Index<&VdBsqHypothesisIdx<'sess>> for VdBsqHypothesisArena<'sess> {
    type Output = VdBsqHypothesisEntry<'sess>;

    fn index(&self, index: &VdBsqHypothesisIdx<'sess>) -> &Self::Output {
        &self.0[index.0]
    }
}

impl<'sess> VdBsqHypothesisArena<'sess> {
    pub(crate) fn alloc_one(
        &mut self,
        entry: VdBsqHypothesisEntry<'sess>,
    ) -> VdBsqHypothesisIdx<'sess> {
        let idx = self.0.alloc_one(entry);
        VdBsqHypothesisIdx(idx)
    }
}

impl<'sess> VdBsqHypothesisEntry<'sess> {
    pub fn expr(&self) -> VdBsqExprFld<'sess> {
        self.prop
    }

    pub fn construction(&self) -> &VdBsqHypothesisConstruction<'sess> {
        &self.construction
    }
}

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub(crate) fn transcribe_hypothesis(
        &self,
        hypothesis: VdBsqHypothesisIdx<'sess>,
        explicit_prop: Option<VdMirExprIdx>,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirHypothesisIdx {
        hypothesis_constructor.construct_new_hypothesis(hypothesis, |hypothesis_constructor| {
            self.transcribe_hypothesis_inner(hypothesis, explicit_prop, hypothesis_constructor)
        })
    }

    fn transcribe_hypothesis_inner(
        &self,
        hypothesis: VdBsqHypothesisIdx<'sess>,
        explicit_prop: Option<VdMirExprIdx>,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> (VdMirExprIdx, VdMirHypothesisConstruction) {
        let hypothesis_entry = &self.hypothesis_constructor.arena()[hypothesis];
        let construction = match *self.hypothesis_constructor.arena()[hypothesis].construction() {
            VdBsqHypothesisConstruction::Sorry => VdMirHypothesisConstruction::Sorry,
            VdBsqHypothesisConstruction::TermTrivial(b) => {
                VdMirHypothesisConstruction::TermTrivial(b)
            }
            VdBsqHypothesisConstruction::Apply {
                path,
                is_real_coercion,
            } => VdMirHypothesisConstruction::Apply {
                path,
                is_real_coercion: self
                    .transcribe_coercion(is_real_coercion, hypothesis_constructor),
            },
            VdBsqHypothesisConstruction::Assume => VdMirHypothesisConstruction::Assume,
            VdBsqHypothesisConstruction::TermEquivalence {
                hypothesis: src_hypothesis,
            } => VdMirHypothesisConstruction::TermEquivalence {
                hypothesis: self.transcribe_hypothesis(
                    src_hypothesis,
                    None,
                    hypothesis_constructor,
                ),
                derivation_chunk: self.transcribe_term_derivation(
                    hypothesis,
                    src_hypothesis,
                    hypothesis_constructor,
                ),
            },
            VdBsqHypothesisConstruction::CommRing => VdMirHypothesisConstruction::CommRing,
            VdBsqHypothesisConstruction::LetAssigned => VdMirHypothesisConstruction::LetAssigned,
            VdBsqHypothesisConstruction::LitnumReduce => VdMirHypothesisConstruction::LitnumReduce,
            VdBsqHypothesisConstruction::LitnumBound => VdMirHypothesisConstruction::LitnumBound,
        };
        let prop = match explicit_prop {
            Some(prop) => prop,
            None => hypothesis_entry
                .expr()
                .transcribe(self, hypothesis_constructor),
        };
        (prop, construction)
    }
}
