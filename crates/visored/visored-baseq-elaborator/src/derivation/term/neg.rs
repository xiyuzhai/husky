use super::*;

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub(super) fn transcribe_neg_term_derivation_construction(
        &mut self,
        opd: VdBsqExpr<'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirTermDerivationConstruction {
        let minus_one_mul_opd = self.mk_mul(self.mk_i128(-1), opd, hc);
        let minus_one_mul_opd_nf = self.transcribe_expr_term_derivation(minus_one_mul_opd, hc);
        VdMirTermDerivationConstruction::NegAtom {
            minus_one_mul_a_nf: minus_one_mul_opd_nf.derivation(),
        }
    }
}
