use super::*;
use crate::tactic::VdBsqTactic;
use alt_maybe_result::*;
use alt_option::*;
use elaborator::VdBsqElaboratorInner;
use expr::VdBsqExpr;
use hypothesis::{
    construction::VdBsqHypothesisConstruction, contradiction::VdBsqHypothesisResult,
    VdBsqHypothesisIdx,
};
use visored_mir_expr::{expr::VdMirExprIdx, hint::VdMirHintIdx, stmt::VdMirStmtIdx};

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub fn obvious(&mut self, prop: VdBsqExpr<'sess>) -> Mhr<'sess> {
        self.with_call(VdBsqStrategyCall::Obvious, |slf| slf.obvious_inner(prop))
    }

    fn obvious_inner(&mut self, prop: VdBsqExpr<'sess>) -> Mhr<'sess> {
        for tactic in self.session().obvious_tactics() {
            tactic.run(prop, self)?
        }
        AltJustOk(Ok(self.hc.construct_new_hypothesis(
            prop,
            VdBsqHypothesisConstruction::Sorry,
        )))
    }
}

#[deprecated = "TODO: load tactics from a file"]
pub fn load_obvious_tactics() -> Vec<VdBsqTactic> {
    vec![
        // order matters!!!
        // assumption should always be the first tactic
        VdBsqTactic::Assumption,
        VdBsqTactic::TermTrivial,
        VdBsqTactic::Kurapika,
        VdBsqTactic::LitnumReduce,
        VdBsqTactic::LitnumEstimate,
        VdBsqTactic::CommRing,
        VdBsqTactic::LibrarySearch,
    ]
}
