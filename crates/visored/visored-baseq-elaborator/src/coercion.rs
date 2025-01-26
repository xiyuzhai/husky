pub mod number;

use crate::{
    elaborator::VdBsqElaboratorInner,
    expr::VdBsqExpr,
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
    coercion::VdMirCoercionConstruction, elaborator::linear::IsVdMirSequentialElaboratorInner,
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
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirCoercionConstruction {
        match coercion {
            VdBsqCoercion::Trivial(vd_baseq_trivial_coercion) => VdMirCoercionConstruction::Trivial,
            VdBsqCoercion::Obvious(hypothesis) => VdMirCoercionConstruction::Obvious(
                self.transcribe_implicit_hypothesis(hypothesis, hc),
            ),
        }
    }
}
