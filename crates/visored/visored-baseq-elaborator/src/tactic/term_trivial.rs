use super::*;
use crate::{
    hypothesis::construction::VdBsqHypothesisConstruction,
    term::{prop::VdBsqPropTerm, VdBsqTerm},
};
use alt_maybe_result::*;

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub(crate) fn term_trivial(&mut self, prop: VdBsqExpr<'sess>) -> Mhr<'sess> {
        self.with_call(VdBsqTacticCall::TermTrivial, |slf| {
            slf.term_trivial_inner(prop)
        })
    }

    fn term_trivial_inner(&mut self, prop: VdBsqExpr<'sess>) -> Mhr<'sess> {
        debug_assert!(
            self.hc
                .stack()
                .get_active_hypothesis_with_expr(prop)
                .is_none(),
            "term_trivial should only be called on a fresh prop"
        );
        let VdBsqTerm::Prop(VdBsqPropTerm::Trivial(b)) = prop.term() else {
            return AltNothing;
        };
        match b {
            true => AltJustOk(Ok(self.hc.construct_new_hypothesis(
                prop,
                VdBsqHypothesisConstruction::TermTrivial(b),
            ))),
            false => todo!("raise error"),
        }
    }
}
