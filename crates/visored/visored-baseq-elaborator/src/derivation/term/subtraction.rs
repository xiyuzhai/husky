use super::*;

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub(super) fn transcribe_sub_term_derivation_construction(
        &mut self,
        lopd: VdBsqExprFld<'sess>,
        ropd: VdBsqExprFld<'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirTermDerivationConstruction {
        let add_neg = self.mk_add(lopd, self.mk_neg(ropd, None, hc), None, hc);
        VdMirTermDerivationConstruction::SubEqsAddNeg {
            add_neg: self
                .transcribe_expr_term_derivation(add_neg, hc)
                .derivation(),
        }
    }
}
