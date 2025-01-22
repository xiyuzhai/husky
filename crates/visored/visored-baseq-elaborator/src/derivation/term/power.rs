use super::*;

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub(super) fn transcribe_pow_term_derivation_construction(
        &mut self,
        base: VdBsqExpr<'sess>,
        exponent: VdBsqExpr<'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirTermDerivationConstruction {
        let base = base.normalize(self, hc);
        if exponent.is_one() {
            return VdMirTermDerivationConstruction::PowerOne {
                base: base.derivation(),
            };
        }
        let exponent = exponent.normalize(self, hc);

        todo!()
        // VdMirTermDerivationConstruction::NonReducedPower {
        //     base: base.derivation(),
        //     exponent: exponent.derivation(),
        // }
    }
}
