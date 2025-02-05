use super::*;
use visored_mir_expr::coercion::VdMirSeparatorCoercion;
use visored_mir_opr::separator::chaining::{
    VdMirBaseChainingSeparator, VdMirBaseComparisonSeparator, VdMirBaseRelationSeparator,
};
use visored_signature::signature::separator::base::chaining::VdBaseChainingSeparatorSignature;

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub(super) fn transcribe_chaining_separated_list_term_derivation_construction(
        &mut self,
        leader: VdBsqExpr<'sess>,
        followers: &[(VdBaseChainingSeparatorSignature, VdBsqExpr<'sess>)],
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirTermDerivationConstruction {
        let leader = self.transcribe_expr_term_derivation(leader, hc);
        let followers = followers
            .iter()
            .map(|&(func, follower)| (func, self.transcribe_expr_term_derivation(follower, hc)))
            .collect::<Vec<_>>();
        match followers.len() {
            0 => unreachable!(),
            1 => {
                let (signature, follower) = followers[0];
                self.transcribe_trivial_chaining_separated_list_term_derivation_construction(
                    leader, signature, follower, hc,
                )
            }
            _ => todo!(),
        }
    }

    fn transcribe_trivial_chaining_separated_list_term_derivation_construction(
        &mut self,
        leader: VdBsqExprNormalized<'sess>,
        signature: VdBaseChainingSeparatorSignature,
        follower: VdBsqExprNormalized<'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirTermDerivationConstruction {
        match signature.separator() {
            VdMirBaseChainingSeparator::Iff => todo!(),
            VdMirBaseChainingSeparator::Relation(separator) => match separator {
                VdMirBaseRelationSeparator::Comparison(separator) => self
                    .transcribe_comparison_chaining_separated_list_term_derivation_construction(
                        leader, signature, separator, follower, hc,
                    ),
                VdMirBaseRelationSeparator::Containment(separator) => todo!(),
            },
        }
    }

    fn transcribe_comparison_chaining_separated_list_term_derivation_construction(
        &mut self,
        leader: VdBsqExprNormalized<'sess>,
        signature: VdBaseChainingSeparatorSignature,
        separator: VdMirBaseComparisonSeparator,
        follower: VdBsqExprNormalized<'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirTermDerivationConstruction {
        let db = self.eterner_db();
        if leader.ty().is_numeric(db) {
            self.transcribe_num_comparison_chaining_separated_list_term_derivation_construction(
                leader, signature, separator, follower, hc,
            )
        } else {
            todo!()
        }
    }

    fn transcribe_num_comparison_chaining_separated_list_term_derivation_construction(
        &mut self,
        a_nf: VdBsqExprNormalized<'sess>,
        signature: VdBaseChainingSeparatorSignature,
        separator: VdMirBaseComparisonSeparator,
        b_nf: VdBsqExprNormalized<'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirTermDerivationConstruction {
        let a_sub_b = self.mk_sub(**a_nf, **b_nf);
        let a_ty = a_nf.expr().ty();
        let b_ty = b_nf.expr().ty();
        let ab_ty = a_sub_b.ty();
        VdMirTermDerivationConstruction::NumComparison {
            separator,
            a_nf: a_nf.derivation(),
            b_nf: b_nf.derivation(),
            a_nf_sub_b_nf_nf: self
                .transcribe_expr_term_derivation(a_sub_b, hc)
                .derivation(),
            a_eq_coercion: VdMirSeparatorCoercion::new_eq(a_ty, ab_ty),
            b_eq_coercion: VdMirSeparatorCoercion::new_eq(b_ty, ab_ty),
        }
    }
}
