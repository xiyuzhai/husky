use super::*;
use visored_mir_expr::coercion::{VdMirPrefixOprCoercion, VdMirSeparatorCoercion};
use visored_signature::signature::binary_opr::base::VdBaseBinaryOprSignature;

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub(super) fn transcribe_sub_term_derivation_construction(
        &mut self,
        lopd: VdBsqExpr<'sess>,
        signature: VdBaseBinaryOprSignature,
        ropd: VdBsqExpr<'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirTermDerivationConstruction {
        let add_neg = self.mk_add(lopd, self.mk_neg(ropd, hc), hc);
        let source_ty = ropd.ty();
        let target_ty = signature.ropd_ty();
        VdMirTermDerivationConstruction::SubEqsAddNeg {
            add_neg: self
                .transcribe_expr_term_derivation(add_neg, hc)
                .derivation(),
            b_neg_coercion: VdMirPrefixOprCoercion::new(
                VdMirBasePrefixOpr::RING_NEG,
                source_ty,
                target_ty,
            ),
        }
    }
}
