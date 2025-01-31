use super::product::derive_product;
use super::*;
use crate::term::{comnum::VdBsqComnumTerm, VdBsqTerm};
use visored_mir_expr::coercion::VdMirBinaryOprCoercion;
use visored_opr::opr::binary::VdBaseBinaryOpr;
use visored_signature::signature::binary_opr::{
    base::VdBaseBinaryOprSignature, VdBinaryOprSignature,
};

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub(super) fn transcribe_div_term_derivation_construction(
        &mut self,
        a: VdBsqExpr<'sess>,
        signature: VdBaseBinaryOprSignature,
        b: VdBsqExpr<'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirTermDerivationConstruction {
        let a_nf = a.normalize(self, hc);
        let b_nf = b.normalize(self, hc);
        let a_nf_div_b_nf_dn = derive_div(a_nf, b_nf, self, hc);
        assert_eq!(signature.opr, VdMirBaseBinaryOpr::CommFieldDiv);
        let a_coercion = VdMirBinaryOprCoercion::new(
            VdMirBaseBinaryOpr::CommFieldDiv,
            a_nf.ty(),
            signature.lopd_ty,
        );
        let b_coercion = VdMirBinaryOprCoercion::new(
            VdMirBaseBinaryOpr::CommFieldDiv,
            b_nf.ty(),
            signature.ropd_ty,
        );
        VdMirTermDerivationConstruction::DivEq {
            a_dn: a_nf.derivation(),
            b_dn: b_nf.derivation(),
            a_coercion,
            b_coercion,
            a_nf_div_b_nf_dn: a_nf_div_b_nf_dn.derivation(),
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
