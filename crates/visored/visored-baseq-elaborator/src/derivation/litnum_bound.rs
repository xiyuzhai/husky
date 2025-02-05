use crate::term::litnum::VdBsqLitnumTerm;

use super::*;
use expr::VdBsqExpr;
use foundations::opr::separator::relation::comparison::{VdBsqBoundBoundaryKind, VdBsqBoundOpr};
use hypothesis::stashes::litnum_bound::{VdBsqLitnumBound, VdBsqLitnumBoundSrc};
use visored_mir_expr::{
    coercion::{VdMirBinaryOprCoercion, VdMirSeparatorCoercion},
    derivation::{
        chunk::VdMirDerivationChunk,
        construction::litnum_bound::{
            VdMirLitnumBoundDerivationConstruction, VdMirLitnumBoundDerivationIdx,
        },
    },
    hypothesis::constructor::VdMirHypothesisConstructor,
};
use visored_mir_opr::separator::chaining::VdMirBaseComparisonSeparator;
use visored_opr::separator::VdBaseSeparator;
use visored_signature::signature::separator::base::chaining::{
    relation::VdBaseRelationSeparatorSignature, VdBaseChainingSeparatorSignature,
};

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess>
where
    'db: 'sess,
{
    pub fn transcribe_litnum_bound_derivation(
        &mut self,
        dst: VdBsqHypothesisIdx<'sess>,
        bound: VdBsqLitnumBound<'sess>,
        opr: VdBsqBoundOpr,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirDerivationChunk {
        hc.obtain_derivation_chunk_within_hypothesis(|hc| {
            let prop = self.hc.arena()[dst].prop().transcribe(None, self, hc);
            let src = bound.src();
            let a_opr = match bound.boundary_kind() {
                VdBsqBoundBoundaryKind::Closed => VdMirBaseComparisonSeparator::GE,
                VdBsqBoundBoundaryKind::Open => VdMirBaseComparisonSeparator::GT,
            };
            let b_opr = match opr {
                VdBsqBoundOpr::Le | VdBsqBoundOpr::Ge => VdMirBaseComparisonSeparator::GE,
                VdBsqBoundOpr::Lt | VdBsqBoundOpr::Gt => VdMirBaseComparisonSeparator::GT,
            };
            let (src_nf, src_nf_dn) =
                normalize_litnum_bound(src.litnum_factor(), src.hypothesis(), self, hc);
            let (dst_nf, dst_nf_dn) = normalize_litnum_bound(bound.litnum_factor(), dst, self, hc);
            let src_diff = self.mk_sub(src_nf, self.mk_litnum(src.litnum_summand()));
            let dst_diff = self.mk_sub(dst_nf, self.mk_litnum(bound.litnum_summand()));
            let src_nf_and_dst_nf_equivalence_dn = self
                .transcribe_non_trivial_expr_equivalence_term_derivation(src_diff, dst_diff, hc);
            let src = src.hypothesis().transcribe(self, None, hc);
            let a_ty = src_diff.ty();
            let b_ty = dst_diff.ty();
            let ab_ty = hc.infer_eq_signature(a_ty, b_ty).left_item_ty();
            let src_sub_coercion = VdMirBinaryOprCoercion::new_sub(a_ty, ab_ty);
            let dst_sub_coercion = VdMirBinaryOprCoercion::new_sub(b_ty, ab_ty);
            let src_cmp_coercion = VdMirSeparatorCoercion::new(a_opr.into(), a_ty, ab_ty);
            let dst_cmp_coercion = VdMirSeparatorCoercion::new(b_opr.into(), b_ty, ab_ty);
            hc.alloc_derivation(
                prop,
                VdMirLitnumBoundDerivationConstruction::Finish {
                    a_opr,
                    b_opr,
                    src,
                    src_nf_dn,
                    dst_nf_dn,
                    src_nf_and_dst_nf_equivalence_dn,
                    src_sub_coercion,
                    dst_sub_coercion,
                    src_cmp_coercion,
                    dst_cmp_coercion,
                }
                .into(),
            )
        })
    }
}

fn normalize_litnum_bound<'db, 'sess>(
    litnum_factor: VdBsqLitnumTerm<'sess>,
    hypothesis: VdBsqHypothesisIdx<'sess>,
    elr: &VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> (VdBsqExpr<'sess>, VdMirLitnumBoundDerivationIdx) {
    let litnum_factor = elr.mk_litnum(litnum_factor);
    let prop = elr.hc.arena()[hypothesis].prop();
    let (lhs, signature, rhs) = prop.split_trivial_chaining_separated_list(elr, hc);
    let expr = elr.mk_sub(lhs, rhs);
    let expr = elr.mk_div(expr, litnum_factor);
    let VdBaseChainingSeparatorSignature::Relation(VdBaseRelationSeparatorSignature::Comparison(
        signature,
    )) = signature
    else {
        unreachable!()
    };
    let prop_nf = match signature.separator() {
        VdMirBaseComparisonSeparator::Eq | VdMirBaseComparisonSeparator::Ne => unreachable!(),
        VdMirBaseComparisonSeparator::Lt | VdMirBaseComparisonSeparator::Gt => elr
            .mk_trivial_chaining_separated_list(
                expr,
                VdBaseSeparator::GT,
                elr.mk_litnum(VdBsqLitnumTerm::Int128(0)),
                hc,
            ),
        VdMirBaseComparisonSeparator::Le | VdMirBaseComparisonSeparator::Ge => elr
            .mk_trivial_chaining_separated_list(
                expr,
                VdBaseSeparator::GE,
                elr.mk_litnum(VdBsqLitnumTerm::Int128(0)),
                hc,
            ),
    };
    let dn_prop = elr.mk_iff(prop, prop_nf, hc).transcribe(None, elr, hc);
    let dn = hc.alloc_litnum_bound_derivation(
        dn_prop,
        VdMirLitnumBoundDerivationConstruction::Normalize {
            separator: signature.separator(),
        },
    );
    (expr, dn)
}
