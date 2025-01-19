use super::*;
use visored_signature::signature::separator::base::folding::VdBaseFoldingSeparatorSignature;

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub(super) fn transcribe_sum_term_derivation_construction(
        &mut self,
        leader: VdBsqExpr<'sess>,
        followers: &[(VdBaseFoldingSeparatorSignature, VdBsqExpr<'sess>)],
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirTermDerivationConstruction {
        let (lopd, signature, ropd) = match followers.len() {
            0 => unreachable!(),
            1 => {
                let (signature, follower) = followers[0];
                if let (&VdBsqExprData::Literal(leader), &VdBsqExprData::Literal(follower)) =
                    (leader.data(), follower.data())
                {
                    return VdMirTermDerivationConstruction::LiteralAdd;
                }
                (leader, signature, follower)
            }
            _ => {
                let last_signature = followers.last().unwrap().0;
                let lopd = self.mk_expr(
                    VdBsqExprData::FoldingSeparatedList {
                        leader,
                        followers: followers[..followers.len() - 1].to_smallvec(),
                    },
                    followers[followers.len() - 2].0.expr_ty(),
                );
                let signature = followers.last().unwrap().0;
                let ropd = followers.last().unwrap().1;
                (lopd, signature, ropd)
            }
        };
        let expected_ty = signature.expr_ty();
        let lopd = lopd.normalize(self, hc);
        let ropd = ropd.normalize(self, hc);
        let sum = self.mk_add(lopd.expr(), ropd.expr(), hc);
        // let sum = sum.normalize(self, hc);
        VdMirTermDerivationConstruction::AddEq {
            lopd: lopd.derivation(),
            ropd: ropd.derivation(),
            sum: todo!(),
        }
    }
}
