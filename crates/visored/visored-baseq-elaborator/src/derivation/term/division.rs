use super::product::derive_product;
use super::*;
use crate::term::{comnum::VdBsqComnumTerm, VdBsqTerm};

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub(super) fn transcribe_div_term_derivation_construction(
        &mut self,
        numerator: VdBsqExpr<'sess>,
        denominator: VdBsqExpr<'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirTermDerivationConstruction {
        let numerator_nf = numerator.normalize(self, hc);
        let denominator_nf = denominator.normalize(self, hc);
        let numerator_dn_div_denominator_dn_nf = derive_div(numerator_nf, denominator_nf, self, hc);
        VdMirTermDerivationConstruction::DivEq {
            numerator_dn: numerator_nf.derivation(),
            denominator_dn: denominator_nf.derivation(),
            numerator_dn_div_denominator_dn_dn: numerator_dn_div_denominator_dn_nf.derivation(),
        }
    }
}

fn derive_div<'db, 'sess>(
    numerator: VdBsqExprNormalized<'sess>,
    denominator: VdBsqExprNormalized<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdBsqExprNormalized<'sess> {
    let construction = derive_div_construction(numerator, denominator, elr, hc);
    let expr = elr.mk_div(**numerator, **denominator, hc);
    VdBsqExprNormalized::new(expr, construction, elr, hc)
}

fn derive_div_construction<'db, 'sess>(
    numerator: VdBsqExprNormalized<'sess>,
    denominator: VdBsqExprNormalized<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdMirTermDerivationConstruction {
    match denominator.term() {
        VdBsqTerm::Litnum(denominator_term) => {
            let Some(denominator_inv) = denominator_term.inv(elr.floater_db()) else {
                todo!()
            };
            let a_mul_b_inv_dn =
                derive_product(**numerator, elr.mk_litnum(denominator_inv), elr, hc);
            VdMirTermDerivationConstruction::DivLiteral {
                a_mul_b_inv_dn: a_mul_b_inv_dn.derivation(),
            }
        }
        VdBsqTerm::Comnum(denominator_term) => match denominator_term {
            VdBsqComnumTerm::Atom(denominator_term) => {
                let a = **numerator;
                let b = **denominator;
                let a_mul_b_inv_dn = derive_product(a, elr.mk_inv(b, hc), elr, hc);
                VdMirTermDerivationConstruction::DivAtom {
                    a_mul_b_inv_dn: a_mul_b_inv_dn.derivation(),
                }
            }
            VdBsqComnumTerm::Sum(denominator) => todo!(),
            VdBsqComnumTerm::Product(denominator) => todo!(),
        },
        VdBsqTerm::Prop(denominator) => todo!(),
        VdBsqTerm::Set(denominator) => todo!(),
    }
}
