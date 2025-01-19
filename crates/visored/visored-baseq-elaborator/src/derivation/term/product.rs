use super::*;
use visored_signature::signature::separator::base::folding::VdBaseFoldingSeparatorSignature;

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub(super) fn transcribe_product_term_derivation_construction(
        &mut self,
        leader: VdBsqExpr<'sess>,
        followers: &[(VdBaseFoldingSeparatorSignature, VdBsqExpr<'sess>)],
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirTermDerivationConstruction {
        for (signature, _) in followers {
            assert_eq!(
                signature.separator(),
                VdMirBaseFoldingSeparator::CommRingAdd.into()
            );
        }
        let leader_equivalence = self.transcribe_expr_term_derivation(leader, hc);
        let follower_equivalences = followers
            .iter()
            .map(|&(func, follower)| (func, self.transcribe_expr_term_derivation(follower, hc)))
            .collect::<Vec<_>>();
        todo!()
    }
}
