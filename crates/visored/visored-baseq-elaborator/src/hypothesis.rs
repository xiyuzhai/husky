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

impl<'db, 'sess> VdBsqHypothesisIdx<'sess> {
    pub(crate) fn transcribe(
        self,
        elaborator: &mut VdBsqElaboratorInner<'db, 'sess>,
        explicit_prop: Option<VdMirExprIdx>,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirHypothesisIdx {
        hypothesis_constructor.construct_new_hypothesis(self, |hypothesis_constructor| {
            self.transcribe_inner(explicit_prop, elaborator, hypothesis_constructor)
        })
    }

    fn transcribe_inner(
        self,
        explicit_prop: Option<VdMirExprIdx>,
        elaborator: &mut VdBsqElaboratorInner<'db, 'sess>,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> (VdMirExprIdx, VdMirHypothesisConstruction) {
        let construction = match *elaborator.hypothesis_constructor.arena()[self].construction() {
            VdBsqHypothesisConstruction::Sorry => VdMirHypothesisConstruction::Sorry,
            VdBsqHypothesisConstruction::TermTrivial(b) => {
                VdMirHypothesisConstruction::TermTrivial(b)
            }
            VdBsqHypothesisConstruction::Apply {
                path,
                is_real_coercion,
            } => VdMirHypothesisConstruction::Apply {
                path,
                is_real_coercion: elaborator
                    .transcribe_coercion(is_real_coercion, hypothesis_constructor),
            },
            VdBsqHypothesisConstruction::Assume => VdMirHypothesisConstruction::Assume,
            VdBsqHypothesisConstruction::TermEquivalence {
                hypothesis: src_hypothesis,
            } => VdMirHypothesisConstruction::TermEquivalence {
                hypothesis: src_hypothesis.transcribe(elaborator, None, hypothesis_constructor),
                derivation_chunk: elaborator.transcribe_term_derivation(
                    src_hypothesis,
                    self,
                    hypothesis_constructor,
                ),
            },
            VdBsqHypothesisConstruction::CommRing => VdMirHypothesisConstruction::CommRing,
            VdBsqHypothesisConstruction::LetAssigned => VdMirHypothesisConstruction::LetAssigned,
            VdBsqHypothesisConstruction::LitnumReduce => VdMirHypothesisConstruction::LitnumReduce,
            VdBsqHypothesisConstruction::LitnumBound => VdMirHypothesisConstruction::LitnumBound,
        };
        let hypothesis_entry = &elaborator.hypothesis_constructor.arena()[self];
        let prop = match explicit_prop {
            Some(prop) => prop,
            None => hypothesis_entry
                .expr()
                .transcribe(elaborator, hypothesis_constructor),
        };
        (prop, construction)
    }
}
