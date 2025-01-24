use super::product::derive_product;
use super::*;
use crate::term::VdBsqTerm;

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub(super) fn transcribe_div_term_derivation_construction(
        &mut self,
        numerator: VdBsqExpr<'sess>,
        denominator: VdBsqExpr<'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirTermDerivationConstruction {
        let numerator_nf = numerator.normalize(self, hc);
        let denominator_nf = denominator.normalize(self, hc);
        let numerator_dn_div_denominator_dn_nf =
            derive_div(numerator_nf.derived(), denominator_nf.derived(), self, hc);
        VdMirTermDerivationConstruction::DivEq {
            numerator_dn: numerator_nf.derivation(),
            denominator_dn: denominator_nf.derivation(),
            numerator_dn_div_denominator_dn_dn: numerator_dn_div_denominator_dn_nf.derivation(),
        }
    }
}

fn derive_div<'db, 'sess>(
    numerator: VdBsqExpr<'sess>,
    denominator: VdBsqExpr<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdBsqExprNormalized<'sess> {
    let construction = derive_div_construction(numerator, denominator, elr, hc);
    let expr = elr.mk_div(numerator, denominator, hc);
    VdBsqExprNormalized::new(expr, construction, elr, hc)
}

fn derive_div_construction<'db, 'sess>(
    numerator: VdBsqExpr<'sess>,
    denominator: VdBsqExpr<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdMirTermDerivationConstruction {
    match denominator.term() {
        VdBsqTerm::Litnum(denominator) => {
            let Some(denominator_inv) = denominator.inv(elr.floater_db()) else {
                todo!()
            };
            let a_mul_b_inv_dn = derive_product(numerator, elr.mk_litnum(denominator_inv), elr, hc);
            VdMirTermDerivationConstruction::DivLiteral {
                a_mul_b_inv_dn: todo!(),
            }
        }
        VdBsqTerm::Comnum(vd_bsq_comnum_term) => todo!(),
        VdBsqTerm::Prop(vd_bsq_prop_term) => todo!(),
        VdBsqTerm::Set(vd_bsq_set_term) => todo!(),
    }
}
