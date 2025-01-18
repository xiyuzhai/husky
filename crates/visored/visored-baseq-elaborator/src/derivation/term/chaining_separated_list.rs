use super::*;
use visored_mir_opr::separator::chaining::{
    VdMirBaseChainingSeparator, VdMirBaseComparisonSeparator, VdMirBaseRelationSeparator,
};
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
                let follower = followers[0].1;
                let (signature, follower_equivalence) = follower_equivalences[0];
                self.transcribe_trivial_chaining_separated_list_term_derivation_construction(
                    leader,
                    leader_equivalence,
                    signature,
                    follower,
                    follower_equivalence,
                    hc,
                )
            }
            _ => todo!(),
        }
    }

    fn transcribe_trivial_chaining_separated_list_term_derivation_construction(
        &mut self,
        leader: VdBsqExprFld<'sess>,
        leader_equivalence: VdMirDerivationIdx,
        signature: VdBaseChainingSeparatorSignature,
        follower: VdBsqExprFld<'sess>,
        follower_equivalence: VdMirDerivationIdx,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirTermDerivationConstruction {
        match signature.separator() {
            VdMirBaseChainingSeparator::Iff => todo!(),
            VdMirBaseChainingSeparator::Relation(separator) => match separator {
                VdMirBaseRelationSeparator::Comparison(separator) => self
                    .transcribe_comparison_chaining_separated_list_term_derivation_construction(
                        leader,
                        leader_equivalence,
                        signature,
                        separator,
                        follower,
                        follower_equivalence,
                        hc,
                    ),
                VdMirBaseRelationSeparator::Containment(separator) => todo!(),
            },
        }
    }

    fn transcribe_comparison_chaining_separated_list_term_derivation_construction(
        &mut self,
        leader: VdBsqExprFld<'sess>,
        leader_equivalence: VdMirDerivationIdx,
        signature: VdBaseChainingSeparatorSignature,
        separator: VdMirBaseComparisonSeparator,
        follower: VdBsqExprFld<'sess>,
        follower_equivalence: VdMirDerivationIdx,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirTermDerivationConstruction {
        let db = self.eterner_db();
        if leader.ty().is_numeric(db) {
            self.transcribe_num_comparison_chaining_separated_list_term_derivation_construction(
                leader,
                leader_equivalence,
                signature,
                separator,
                follower,
                follower_equivalence,
                hc,
            )
        } else {
            todo!()
        }
    }

    fn transcribe_num_comparison_chaining_separated_list_term_derivation_construction(
        &mut self,
        lhs: VdBsqExprFld<'sess>,
        leader_equivalence: VdMirDerivationIdx,
        signature: VdBaseChainingSeparatorSignature,
        separator: VdMirBaseComparisonSeparator,
        rhs: VdBsqExprFld<'sess>,
        follower_equivalence: VdMirDerivationIdx,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirTermDerivationConstruction {
        let lhs_minus_rhs = self.mk_sub(lhs, rhs, None, hc);
        VdMirTermDerivationConstruction::NumComparison {
            lhs_minus_rhs: self.transcribe_expr_term_derivation(lhs_minus_rhs, hc),
        }
    }
}
