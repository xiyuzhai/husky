use super::*;

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub(crate) fn assumption_or_trivial(&mut self, prop: VdBsqExpr<'sess>) -> Mhr<'sess> {
        self.with_call(VdBsqTacticCall::Assumption, |slf| {
            slf.assumption_or_trivial_inner(prop)
        })
    }

    fn assumption_or_trivial_inner(&mut self, prop: VdBsqExpr<'sess>) -> Mhr<'sess> {
        AltJustOk(Ok(self.hc.assumption_or_trivial(prop)?))
    }
}
