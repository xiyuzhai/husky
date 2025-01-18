use super::*;

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub(super) fn transcribe_sub_term_derivation_construction(
        &mut self,
        lopd: VdBsqExprFld<'sess>,
        ropd: VdBsqExprFld<'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirTermDerivationConstruction {
        let lopd = self.transcribe_expr_term_derivation(lopd, hc);
        let ropd = self.transcribe_expr_term_derivation(ropd, hc);
        todo!()
    }
}
