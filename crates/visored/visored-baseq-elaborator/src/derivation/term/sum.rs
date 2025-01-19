use super::*;
use visored_signature::signature::separator::base::folding::VdBaseFoldingSeparatorSignature;

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub(super) fn transcribe_sum_term_derivation_construction(
        &mut self,
        leader: VdBsqExpr<'sess>,
        followers: &[(VdBaseFoldingSeparatorSignature, VdBsqExpr<'sess>)],
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirTermDerivationConstruction {
        if let &[(signature, follower)] = followers {
            if let (&VdBsqExprData::Literal(leader), &VdBsqExprData::Literal(follower)) =
                (leader.data(), follower.data())
            {
                return VdMirTermDerivationConstruction::LiteralAdd;
            }
        }
        let (lopd, signature, ropd) = self.split_folding_separated_list(leader, followers);
        let expected_ty = signature.expr_ty();
        let lopd = lopd.normalize(self, hc);
        let ropd = ropd.normalize(self, hc);
        VdMirTermDerivationConstruction::AddEq {
            lopd: lopd.derivation(),
            ropd: ropd.derivation(),
            merge: merge(lopd.expr(), ropd.expr(), self, hc).derivation(),
        }
    }
}

fn merge<'db, 'sess>(
    lopd: VdBsqExpr<'sess>,
    ropd: VdBsqExpr<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdBsqExprNf<'sess> {
    todo!()
}
