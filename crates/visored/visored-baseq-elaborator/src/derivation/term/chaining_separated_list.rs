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
        match follower_equivalences.len() {
            0 => unreachable!(),
            1 => {
                let (signature, follower_equivalence) = follower_equivalences[0];
                self.transcribe_trivial_chaining_separated_list_term_derivation_construction(
                    leader_equivalence,
                    signature,
                    follower_equivalence,
                    hc,
                )
            }
            _ => todo!(),
        }
    }

    fn transcribe_trivial_chaining_separated_list_term_derivation_construction(
        &mut self,
        leader_equivalence: VdMirDerivationIdx,
        signature: VdBaseChainingSeparatorSignature,
        follower_equivalence: VdMirDerivationIdx,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirTermDerivationConstruction {
        todo!()
    }
}
