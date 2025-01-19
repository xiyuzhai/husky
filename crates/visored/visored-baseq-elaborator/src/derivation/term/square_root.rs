use super::*;

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub(super) fn transcribe_sqrt_term_derivation_construction(
        &mut self,
        radicand: VdBsqExpr<'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirTermDerivationConstruction {
        let radicand = self.transcribe_expr_term_derivation(radicand, hc);
        todo!()
    }
}
