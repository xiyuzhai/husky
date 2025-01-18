use super::*;

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub(super) fn transcribe_div_term_derivation_construction(
        &mut self,
        numerator: VdBsqExprFld<'sess>,
        denominator: VdBsqExprFld<'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirTermDerivationConstruction {
        let numerator = self.transcribe_expr_term_derivation(numerator, hc);
        let denominator = self.transcribe_expr_term_derivation(denominator, hc);
        todo!()
    }
}
