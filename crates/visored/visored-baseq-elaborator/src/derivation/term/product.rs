use super::*;
use crate::term::{
    comnum::{product::VdBsqProductStem, VdBsqComnumTerm},
    num::VdBsqNumTerm,
    VdBsqTerm,
};
use sum::derive_add;
use visored_mir_expr::coercion::{
    pow::VdMirPowCoercion, triangle::VdMirCoercionTriangle, VdMirSeparatorCoercion,
};
use visored_signature::signature::separator::base::folding::VdBaseFoldingSeparatorSignature;
use visored_term::term::literal::VdLiteral;

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub(super) fn transcribe_product_term_derivation_construction(
        &mut self,
        leader: VdBsqExpr<'sess>,
        followers: &[(VdBaseFoldingSeparatorSignature, VdBsqExpr<'sess>)],
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirTermDerivationConstruction {
        if let &[(signature, follower)] = followers {
            if let Some(construction) = try_trivial_construction(leader, follower, self, hc) {
                return construction;
            }
        }
        let (a, signature, b) = self.split_folding_separated_list(leader, followers);
        let a_nf = a.normalize(self, hc);
        let b_nf = b.normalize(self, hc);
        let a_eq_coercion = VdMirSeparatorCoercion::new_eq(a.ty(), signature.item_ty());
        let b_eq_coercion = VdMirSeparatorCoercion::new_eq(b.ty(), signature.item_ty());
        VdMirTermDerivationConstruction::MulEq {
            a: a_nf.derivation(),
            b: b_nf.derivation(),
            a_eq_coercion,
            b_eq_coercion,
            merge: derive_product(a_nf.derived(), b_nf.derived(), self, hc).derivation(),
        }
    }
}

fn try_trivial_construction<'db, 'sess>(
    lopd: VdBsqExpr<'sess>,
    ropd: VdBsqExpr<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> Option<VdMirTermDerivationConstruction> {
    if let &VdBsqExprData::Literal(leader) = lopd.data() {
        if leader.is_one() {
            let a_nf = ropd.normalize(elr, hc);
            return Some(VdMirTermDerivationConstruction::OneMul {
                a_nf: a_nf.derivation(),
            });
        } else if let &VdBsqExprData::Literal(follower) = ropd.data() {
            return Some(VdMirTermDerivationConstruction::LiteralMulLiteral);
        }
    }
    None
}

/// Assumes that `lopd` and `ropd` are normalized or parts of normalized expressions.
pub fn derive_product<'db, 'sess>(
    lopd: VdBsqExpr<'sess>,
    ropd: VdBsqExpr<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdBsqExprDerived<'sess> {
    let derived = derive_product_aux(lopd, ropd, elr, hc);
    // the following deals with the case where the end product is of form a litnum multiplying a sum
    // we reduce it to just a sum
    rq!(let VdBsqExprData::FoldingSeparatedList {
        leader,
        ref followers,
    } = *derived.data(), derived);
    rq!(let VdBsqExprData::Literal(leader_literal) = *leader.data(), derived);
    rq!(
        followers.len() == 1
            && followers[0].0.separator() == VdMirBaseFoldingSeparator::COMM_RING_MUL,
        derived
    );
    let follower = followers[0].1;
    rq!(
        let VdBsqExprData::Application {
            function: VdMirFunc::Power(_),
            arguments: ref pow_args,
            ..
        } = *follower.data(), derived);
    rq!(pow_args[1].is_one(), derived);
    let base = pow_args[0];
    rq!(
        let VdBsqExprData::FoldingSeparatedList {
            followers: ref base_followers,
            ..
        } = *base.data(), derived);
    rq!(
        base_followers[0].0.separator() == VdMirBaseFoldingSeparator::COMM_RING_ADD,
        derived
    );
    derive_literal_mul_sum(derived, leader, leader_literal, base, elr, hc)
}

fn derive_product_aux<'db, 'sess>(
    lopd: VdBsqExpr<'sess>,
    ropd: VdBsqExpr<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdBsqExprDerived<'sess> {
    let (construction, derived) = derive_product_construction(lopd, ropd, elr, hc);
    let expr = elr.mk_mul(lopd, ropd, hc);
    VdBsqExprDerived::new(expr, derived, construction, elr, hc)
}

fn derive_product_construction<'db, 'sess>(
    lopd: VdBsqExpr<'sess>,
    ropd: VdBsqExpr<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> (VdMirTermDerivationConstruction, Option<VdBsqExpr<'sess>>) {
    match *ropd.data() {
        VdBsqExprData::Literal(_) => derive_mul_literal(lopd, ropd, elr, hc),
        VdBsqExprData::FoldingSeparatedList { ref followers, .. }
            if followers[0].0.separator() == VdMirBaseFoldingSeparator::COMM_RING_MUL =>
        {
            let (b, rsignature, c) = ropd.split_mul(elr, hc);
            let ab_dn = derive_product_aux(lopd, b, elr, hc);
            let ab_term_mul_c_dn = derive_product_aux(ab_dn.derived(), c, elr, hc);
            let ab_eq_coercion =
                VdMirSeparatorCoercion::new_eq(ab_dn.expr().ty(), ab_term_mul_c_dn.expr().ty());
            let ab_mul_coercion = VdMirSeparatorCoercion::new_comm_ring_mul(
                ab_dn.expr().ty(),
                ab_term_mul_c_dn.expr().ty(),
            );
            let bc_mul_coercion =
                VdMirSeparatorCoercion::new_comm_ring_mul(ropd.ty(), ab_term_mul_c_dn.expr().ty());
            (
                VdMirTermDerivationConstruction::MulProduct {
                    rsignature,
                    ab_nf: ab_dn.derivation(),
                    ab_term_mul_c_nf: ab_term_mul_c_dn.derivation(),
                    ab_eq_coercion,
                    ab_mul_coercion,
                    bc_mul_coercion,
                },
                None,
            )
        }
        VdBsqExprData::ItemPath(vd_item_path) => todo!(),
        VdBsqExprData::Application {
            function: VdMirFunc::NormalBaseSqrt(_),
            ref arguments,
        } => todo!(),
        VdBsqExprData::Application {
            function: VdMirFunc::Power(_),
            ref arguments,
        } => derive_mul_exponential(lopd, ropd, elr, hc),
        _ => derive_mul_base(lopd, ropd, elr, hc),
    }
}

fn derive_mul_literal<'db, 'sess>(
    lopd: VdBsqExpr<'sess>,
    ropd: VdBsqExpr<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> (VdMirTermDerivationConstruction, Option<VdBsqExpr<'sess>>) {
    if ropd.is_one() {
        return (VdMirTermDerivationConstruction::MulOne, None);
    }
    match *lopd.data() {
        VdBsqExprData::Literal(leader) => {
            (VdMirTermDerivationConstruction::LiteralMulLiteral, None)
        }
        VdBsqExprData::Application {
            function,
            ref arguments,
        } => todo!("function = `{:?}`", function),
        VdBsqExprData::FoldingSeparatedList {
            leader,
            ref followers,
        } if followers[0].0.separator() == VdMirBaseFoldingSeparator::CommRingMul => {
            match is_product_simple(leader, followers) {
                true => {
                    let c = leader;
                    let a = followers[0].1;
                    let ac_ty = followers[0].0.expr_ty();
                    let d = ropd;
                    let a_ty = a.ty();
                    let c_ty = c.ty();
                    let d_ty = d.ty();
                    let e = {
                        let VdBsqExprData::Literal(c) = *c.data() else {
                            unreachable!()
                        };
                        let VdBsqExprData::Literal(d) = *d.data() else {
                            unreachable!()
                        };
                        let e = c.mul(d, elr.eterner_db());
                        elr.mk_literal(e)
                    };
                    let e_ty = e.ty();
                    let acd_ty = hc.infer_mul_signature(ac_ty, d_ty).expr_ty();
                    let ae_ty = hc.infer_mul_signature(a_ty, e_ty).expr_ty();
                    (
                        VdMirTermDerivationConstruction::SimpleProductMulLiteral {
                            c_mul_a_mul_coercion: VdMirSeparatorCoercion::new_comm_ring_mul(
                                ac_ty, acd_ty,
                            ),
                            e_mul_a_mul_coercion: VdMirSeparatorCoercion::new_comm_ring_mul(
                                ae_ty, acd_ty,
                            ),
                            a_ae_acd_coercion_triangle: VdMirCoercionTriangle::new(
                                a_ty, ae_ty, acd_ty,
                            ),
                            a_ac_acd_coercion_triangle: VdMirCoercionTriangle::new(
                                a_ty, ac_ty, acd_ty,
                            ),
                            e_ae_acd_coercion_triangle: VdMirCoercionTriangle::new(
                                e_ty, ae_ty, acd_ty,
                            ),
                        },
                        None,
                    )
                }
                false => todo!(),
            }
        }
        _ => {
            let derived = elr.mk_mul(ropd, elr.mk_pow_one(lopd, hc), hc);
            (
                VdMirTermDerivationConstruction::BaseMulLiteral,
                Some(derived),
            )
        }
    }
}

fn derive_mul_exponential<'db, 'sess>(
    lopd: VdBsqExpr<'sess>,
    ropd: VdBsqExpr<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> (VdMirTermDerivationConstruction, Option<VdBsqExpr<'sess>>) {
    let ropd_base = exponential_base(ropd);
    match *lopd.data() {
        VdBsqExprData::Literal(literal) => {
            if literal.is_one() {
                let (base, signature, exponent) = ropd.split_pow(elr, hc);
                if exponent.is_one() {
                    return (VdMirTermDerivationConstruction::OneMulPowerOne, None);
                }
            }
            (VdMirTermDerivationConstruction::Reflection, None)
        }
        VdBsqExprData::FoldingSeparatedList {
            leader,
            ref followers,
        } if followers[0].0.separator() == VdMirBaseFoldingSeparator::COMM_RING_MUL => {
            match leader.data() {
                VdBsqExprData::Literal(vd_literal) => (),
                _ => unreachable!(),
            }
            if is_product_simple(leader, followers) {
                let a_base = exponential_base(followers[0].1);
                let b_base = exponential_base(ropd);
                match a_base.cmp(&b_base) {
                    core::cmp::Ordering::Less => (
                        VdMirTermDerivationConstruction::SimpleProductMulExponentialLess,
                        None,
                    ),
                    core::cmp::Ordering::Equal => todo!(),
                    core::cmp::Ordering::Greater => (
                        VdMirTermDerivationConstruction::SimpleProductMulExponentialGreater,
                        None,
                    ),
                }
            } else {
                todo!()
            }
        }
        VdBsqExprData::Application {
            function: VdMirFunc::Power(signature),
            ref arguments,
        } => todo!("signature = `{:?}`", signature),
        _ => {
            assert!(matches!(
                lopd.term(),
                VdBsqTerm::Comnum(VdBsqComnumTerm::Atom(_))
            ));
            let lopd_base = exponential_base(lopd);
            match lopd_base.cmp(&ropd_base) {
                std::cmp::Ordering::Less => (
                    VdMirTermDerivationConstruction::AtomMulExponentialLess,
                    None,
                ),
                std::cmp::Ordering::Equal => todo!(),
                std::cmp::Ordering::Greater => (
                    VdMirTermDerivationConstruction::AtomMulExponentialGreater,
                    None,
                ),
            }
        }
    }
}

fn is_product_simple<'sess>(
    leader: VdBsqExpr<'sess>,
    followers: &[(VdBaseFoldingSeparatorSignature, VdBsqExpr<'sess>)],
) -> bool {
    assert!(matches!(leader.data(), VdBsqExprData::Literal(_)));
    require!(followers.len() == 1);
    match *followers[0].1.data() {
        VdBsqExprData::FoldingSeparatedList {
            leader,
            ref followers,
        } if followers[0].0.separator() == VdMirBaseFoldingSeparator::COMM_RING_MUL => false,
        _ => true,
    }
}

fn exponential_base<'sess>(expr: VdBsqExpr<'sess>) -> VdBsqNumTerm<'sess> {
    match expr.term() {
        VdBsqTerm::Litnum(vd_bsq_litnum_term) => todo!(),
        VdBsqTerm::Comnum(term) => match term {
            VdBsqComnumTerm::Atom(term) => term.into(),
            VdBsqComnumTerm::Sum(vd_bsq_sum_term) => todo!(),
            VdBsqComnumTerm::Product(term) => {
                assert!(term.litnum_factor().is_one());
                match term.stem() {
                    VdBsqProductStem::Atom(vd_bsq_atom_term) => {
                        todo!()
                    }
                    VdBsqProductStem::NonTrivial(stem) => {
                        assert_eq!(stem.exponentials().len(), 1);
                        stem.exponentials().data()[0].0
                    }
                }
            }
        },
        VdBsqTerm::Prop(vd_bsq_prop_term) => todo!(),
        VdBsqTerm::Set(vd_bsq_set_term) => todo!(),
    }
}

fn derive_mul_base<'db, 'sess>(
    lopd: VdBsqExpr<'sess>,
    ropd: VdBsqExpr<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> (VdMirTermDerivationConstruction, Option<VdBsqExpr<'sess>>) {
    match *lopd.data() {
        VdBsqExprData::Literal(literal) => {
            assert!(!literal.is_one());
            let derived = elr.mk_mul(lopd, elr.mk_pow_one(ropd, hc), hc);
            (
                VdMirTermDerivationConstruction::NonOneLiteralMulAtom,
                Some(derived),
            )
        }
        VdBsqExprData::Variable(..) => {
            let construction = match lopd.term().cmp(&ropd.term()) {
                std::cmp::Ordering::Less => VdMirTermDerivationConstruction::AtomMulAtomLess,
                std::cmp::Ordering::Equal => VdMirTermDerivationConstruction::AtomMulAtomEqual,
                std::cmp::Ordering::Greater => VdMirTermDerivationConstruction::AtomMulAtomGreater,
            };
            (construction, None)
        }
        VdBsqExprData::Application {
            function,
            ref arguments,
        } => todo!(),
        VdBsqExprData::FoldingSeparatedList {
            leader,
            ref followers,
        } => match followers[0].0.separator() {
            VdMirBaseFoldingSeparator::CommRingAdd => todo!(),
            VdMirBaseFoldingSeparator::CommRingMul => {
                if is_product_simple(leader, followers) {
                    let a_base = exponential_base(followers[0].1);
                    let b_base = exponential_base(ropd);
                    match a_base.cmp(&b_base) {
                        core::cmp::Ordering::Less => (
                            VdMirTermDerivationConstruction::SimpleProductMulBaseLess,
                            None,
                        ),
                        core::cmp::Ordering::Equal => todo!(),
                        core::cmp::Ordering::Greater => (
                            VdMirTermDerivationConstruction::SimpleProductMulBaseGreater,
                            None,
                        ),
                    }
                } else {
                    todo!()
                }
            }
            VdMirBaseFoldingSeparator::SetTimes => todo!(),
            VdMirBaseFoldingSeparator::TensorOtimes => todo!(),
        },
        VdBsqExprData::ChainingSeparatedList {
            leader,
            ref followers,
            joined_signature,
        } => todo!(),
        VdBsqExprData::ItemPath(vd_item_path) => todo!(),
    }
}

fn derive_literal_mul_sum<'db, 'sess>(
    p: VdBsqExprDerived<'sess>,
    lopd: VdBsqExpr<'sess>,
    lopd_literal: VdLiteral,
    ropd: VdBsqExpr<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdBsqExprDerived<'sess> {
    if lopd_literal.is_zero() {
        todo!("ZeroMul")
    }
    let a = lopd;
    let (b, _, c) = ropd.split_add(elr, hc);
    let a_mul_b_derivation = derive_product(a, b, elr, hc);
    let ab_ty = a_mul_b_derivation.expr().ty();
    let a_mul_c_derivation = derive_product(a, c, elr, hc);
    let ac_ty = a_mul_c_derivation.expr().ty();
    let ab_term_plus_ac_term_derivation = derive_add(
        a_mul_b_derivation.derived(),
        a_mul_c_derivation.derived(),
        elr,
        hc,
    );
    let abc_ty = ab_term_plus_ac_term_derivation.expr().ty();
    let p_ty = p.expr().ty();
    let a_ty = a.ty();
    let b_ty = b.ty();
    let c_ty = c.ty();
    let bc_ty = ropd.ty();
    let ty_menu = elr.ty_menu();
    VdBsqExprDerived::new(
        p.expr(),
        Some(ab_term_plus_ac_term_derivation.derived()),
        VdMirTermDerivationConstruction::LiteralMulSum {
            p_derivation: p.derivation(),
            a_mul_b_derivation: a_mul_b_derivation.derivation(),
            a_mul_c_derivation: a_mul_c_derivation.derivation(),
            ab_term_plus_ac_term_derivation: ab_term_plus_ac_term_derivation.derivation(),
            pow_coercion: VdMirPowCoercion::new(bc_ty, ty_menu.nat, abc_ty, ty_menu.nat),
            bc_add_coercion: VdMirSeparatorCoercion::new_comm_ring_add(bc_ty, abc_ty),
            ab_eq_coercion: VdMirSeparatorCoercion::new_eq(ab_ty, abc_ty),
            ab_mul_coercion: VdMirSeparatorCoercion::new_comm_ring_mul(ab_ty, abc_ty),
            ac_eq_coercion: VdMirSeparatorCoercion::new_eq(ac_ty, abc_ty),
            ac_mul_coercion: VdMirSeparatorCoercion::new_comm_ring_mul(ac_ty, abc_ty),
            a_ab_abc_coercion_triangle: VdMirCoercionTriangle::new(a_ty, ab_ty, abc_ty),
            a_ac_abc_coercion_triangle: VdMirCoercionTriangle::new(a_ty, ac_ty, abc_ty),
            b_ab_abc_coercion_triangle: VdMirCoercionTriangle::new(b_ty, ab_ty, abc_ty),
            b_bc_abc_coercion_triangle: VdMirCoercionTriangle::new(b_ty, bc_ty, abc_ty),
            c_ac_abc_coercion_triangle: VdMirCoercionTriangle::new(c_ty, ac_ty, abc_ty),
            c_bc_abc_coercion_triangle: VdMirCoercionTriangle::new(c_ty, bc_ty, abc_ty),
            p_coercion: VdMirSeparatorCoercion::new_eq(p_ty, abc_ty),
        },
        elr,
        hc,
    )
}
