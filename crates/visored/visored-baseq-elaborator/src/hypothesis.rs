pub mod construction;
pub mod constructor;
pub mod contradiction;
pub mod region;
pub mod stack;
pub mod stash;
pub mod stashes;

use self::construction::VdBsqHypothesisConstruction;
use crate::{elaborator::VdBsqElaboratorInner, expr::VdBsqExpr};
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
    prop: VdBsqExpr<'sess>,
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
    pub fn expr(&self) -> VdBsqExpr<'sess> {
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
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirHypothesisIdx {
        hc.construct_new_hypothesis(self, |hc| {
            self.transcribe_inner(explicit_prop, elaborator, hc)
        })
    }

    fn transcribe_inner(
        self,
        explicit_prop: Option<VdMirExprIdx>,
        elr: &mut VdBsqElaboratorInner<'db, 'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> (VdMirExprIdx, VdMirHypothesisConstruction) {
        let construction = match *elr.hc.arena()[self].construction() {
            VdBsqHypothesisConstruction::Sorry => VdMirHypothesisConstruction::Sorry,
            VdBsqHypothesisConstruction::TermTrivial(b) => {
                VdMirHypothesisConstruction::TermTrivial(b)
            }
            VdBsqHypothesisConstruction::Apply {
                path,
                is_real_coercion,
            } => VdMirHypothesisConstruction::Apply {
                path,
                is_real_coercion: elr.transcribe_coercion(is_real_coercion, hc),
            },
            VdBsqHypothesisConstruction::Assume => VdMirHypothesisConstruction::Assume,
            VdBsqHypothesisConstruction::TermEquivalence { hypothesis } => {
                VdMirHypothesisConstruction::TermEquivalence {
                    hypothesis: hypothesis.transcribe(elr, None, hc),
                    derivation_chunk: elr.transcribe_term_derivation(hypothesis, self, hc),
                }
            }
            VdBsqHypothesisConstruction::CommRing => VdMirHypothesisConstruction::CommRing,
            VdBsqHypothesisConstruction::LetAssigned => VdMirHypothesisConstruction::LetAssigned,
            VdBsqHypothesisConstruction::LitnumReduce => VdMirHypothesisConstruction::LitnumReduce,
            VdBsqHypothesisConstruction::LitnumBound { src } => {
                VdMirHypothesisConstruction::LitnumBound {
                    derivation_chunk: elr.transcribe_litnum_bound_derivation(self, src, hc),
                }
            }
        };
        let hypothesis_entry = &elr.hc.arena()[self];
        let prop = match explicit_prop {
            Some(prop) => prop,
            None => hypothesis_entry.expr().transcribe(None, elr, hc),
        };
        (prop, construction)
    }
}
