pub mod number;

use crate::{
    elaborator::VdBsqElaboratorInner,
    expr::VdBsqExprFld,
    hypothesis::{
        construction::VdBsqHypothesisConstruction, contradiction::VdBsqHypothesisContradiction,
        VdBsqHypothesisIdx,
    },
};
use either::*;
use visored_entity_path::{
    path::{
        set::{VdPreludeSetPath, VdSetPath},
        VdItemPath,
    },
    theorem::VdTheoremPath,
};
use visored_mir_expr::{
    coercion::VdMirCoercion, elaborator::linear::IsVdMirSequentialElaboratorInner,
    hypothesis::constructor::VdMirHypothesisConstructor,
};
use visored_term::term::VdTerm;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VdBsqCoercionOutcome<'sess> {
    TriviallyTrue(VdBsqTrivialCoercion),
    ObviouslyTrue(VdBsqHypothesisIdx<'sess>),
    Unknown,
    Impossible(VdBsqHypothesisContradiction<'sess>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VdBsqCoercion<'sess> {
    Trivial(VdBsqTrivialCoercion),
    Obvious(VdBsqHypothesisIdx<'sess>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VdBsqTrivialCoercion {
    Identity,
    NumberToReal,
}

impl<'sess> VdBsqCoercionOutcome<'sess> {
    pub fn coercion(self) -> Option<VdBsqCoercion<'sess>> {
        match self {
            VdBsqCoercionOutcome::TriviallyTrue(coercion) => Some(VdBsqCoercion::Trivial(coercion)),
            VdBsqCoercionOutcome::ObviouslyTrue(idx) => Some(VdBsqCoercion::Obvious(idx)),
            VdBsqCoercionOutcome::Unknown => None,
            VdBsqCoercionOutcome::Impossible(_) => None,
        }
    }
}

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub(crate) fn transcribe_coercion(
        &mut self,
        coercion: VdBsqCoercion<'sess>,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirCoercion {
        match coercion {
            VdBsqCoercion::Trivial(vd_baseq_trivial_coercion) => VdMirCoercion::Trivial,
            VdBsqCoercion::Obvious(hypothesis) => VdMirCoercion::Obvious(
                self.transcribe_implicit_hypothesis(hypothesis, hypothesis_constructor),
            ),
        }
    }
}
