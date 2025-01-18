use super::*;

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub(super) fn transcribe_pow_term_derivation_construction(
        &mut self,
        base: VdBsqExprFld<'sess>,
        exponent: VdBsqExprFld<'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirTermDerivationConstruction {
        let base = self.transcribe_expr_term_derivation(base, hc);
        let exponent = self.transcribe_expr_term_derivation(exponent, hc);
        todo!()
    }
}
