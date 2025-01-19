use super::*;

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub(crate) fn assumption(&mut self, prop: VdBsqExpr<'sess>) -> Mhr<'sess> {
        self.with_call(VdBsqTacticCall::Assumption, |slf| {
            slf.assumption_inner(prop)
        })
    }

    fn assumption_inner(&mut self, prop: VdBsqExpr<'sess>) -> Mhr<'sess> {
        AltJustOk(Ok(self.hc.assumption(prop)?))
    }
}
