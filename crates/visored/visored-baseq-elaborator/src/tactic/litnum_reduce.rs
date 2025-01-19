use super::*;
use crate::maneuver::litnum_rewrite::litnum_rewritem;
use crate::{
    coercion::VdBsqCoercionOutcome, expr::VdBsqExprData,
    hypothesis::construction::VdBsqHypothesisConstruction,
};
use alt_option::*;
use term::{prop::VdBsqPropTerm, VdBsqTerm};
use visored_baseq_elaborator_macros::unify_elabm;
use visored_entity_path::{
    path::{
        set::{VdPreludeSetPath, VdSetPath},
        VdItemPath,
    },
    theorem::VdTheoremPath,
};
use visored_mir_expr::expr::application::VdMirFunc;
use visored_mir_opr::separator::VdMirBaseSeparator;
use visored_term::term::VdTerm;

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub(crate) fn litnum_reduce(&mut self, prop: VdBsqExprFld<'sess>) -> Mhr<'sess> {
        self.with_call(VdBsqTacticCall::LitnumReduce, |slf| {
            slf.litnum_reduce_inner(prop)
        })
    }

    fn litnum_reduce_inner(&mut self, prop: VdBsqExprFld<'sess>) -> Mhr<'sess> {
        let rewritem = litnum_rewritem(prop);
        rewritem.eval(self, &|elr, expr| match expr.term() {
            VdBsqTerm::Prop(VdBsqPropTerm::Trivial(b)) => match b {
                true => {
                    let hypothesis = elr
                        .hc
                        .construct_new_hypothesis(prop, VdBsqHypothesisConstruction::LitnumReduce);
                    AltJustOk(Ok(hypothesis))
                }
                false => todo!(),
            },
            _ => AltNothing,
        })
    }
}
