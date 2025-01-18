use super::*;
use visored_signature::signature::separator::base::chaining::VdBaseChainingSeparatorSignature;

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub(super) fn transcribe_chaining_separated_list_term_derivation_construction(
        &mut self,
        leader: VdBsqExprFld<'sess>,
        followers: &[(VdBaseChainingSeparatorSignature, VdBsqExprFld<'sess>)],
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirTermDerivationConstruction {
        let leader_equivalence = self.transcribe_expr_term_derivation(leader, hc);
        let follower_equivalences = followers
            .iter()
            .map(|&(func, follower)| (func, self.transcribe_expr_term_derivation(follower, hc)))
            .collect::<Vec<_>>();
        todo!()
    }
}
