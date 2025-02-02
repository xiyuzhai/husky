use crate::term::{
    comnum::{product::VdBsqProductStem, VdBsqComnumTerm},
    VdBsqTerm,
};

use super::*;
use visored_mir_expr::coercion::{triangle::VdMirCoercionTriangle, VdMirSeparatorCoercion};
use visored_signature::signature::separator::base::folding::VdBaseFoldingSeparatorSignature;
use visored_term::term::literal::VdLiteral;

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub(super) fn transcribe_sum_term_derivation_construction(
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
        let a_normalized = a.normalize(self, hc);
        let b_normalized = b.normalize(self, hc);
        VdMirTermDerivationConstruction::AddEq {
            a_eq_coercion: VdMirSeparatorCoercion::new_eq(a.ty(), signature.item_ty()),
            b_eq_coercion: VdMirSeparatorCoercion::new_eq(b.ty(), signature.item_ty()),
            a_derivation: a_normalized.derivation(),
            b_derivation: b_normalized.derivation(),
            a_term_add_b_term_derivation: derive_add(**a_normalized, **b_normalized, self, hc)
                .derivation(),
        }
    }
}

fn try_trivial_construction<'db, 'sess>(
    lopd: VdBsqExpr<'sess>,
    ropd: VdBsqExpr<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> Option<VdMirTermDerivationConstruction> {
    if let VdBsqExprData::Literal(lopd_lit) = lopd.data() {
        if lopd_lit.is_zero() {
            let a_nf = ropd.normalize(elr, hc);
            return Some(VdMirTermDerivationConstruction::ZeroAdd {
                a_nf: a_nf.derivation(),
            });
        }
        if let VdBsqExprData::Literal(ropd_lit) = ropd.data() {
            return Some(VdMirTermDerivationConstruction::LiteralAddLiteral {
                lopd: *lopd_lit,
                ropd: *ropd_lit,
            });
        }
    }
    None
}

pub(super) fn derive_add<'db, 'sess>(
    lopd: VdBsqExpr<'sess>,
    ropd: VdBsqExpr<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdBsqExprNormalized<'sess> {
    let construction = derive_add_construction(lopd, ropd, elr, hc);
    let expr = elr.mk_add(lopd, ropd, hc);
    VdBsqExprNormalized::new(expr, construction, elr, hc)
}

fn derive_add_construction<'db, 'sess>(
    lopd: VdBsqExpr<'sess>,
    ropd: VdBsqExpr<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdMirTermDerivationConstruction {
    if let Some(construction) = try_trivial_construction(lopd, ropd, elr, hc) {
        return construction;
    }
    match *ropd.data() {
        VdBsqExprData::Literal(ropd_literal) => {
            if ropd_literal.is_zero() {
                VdMirTermDerivationConstruction::NfAddZero
            } else {
                merge_nonzero_literal_construction(lopd, ropd, ropd_literal, elr, hc)
            }
        }
        VdBsqExprData::Variable(lx_math_letter, arena_idx) => {
            let ropd = elr.mk_mul(elr.mk_i128(1), elr.mk_pow(ropd, elr.mk_i128(1), hc), hc);
            let add_product_nf = derive_add(lopd, ropd, elr, hc).derivation();
            VdMirTermDerivationConstruction::AddAtom { add_product_nf }
        }
        VdBsqExprData::Application {
            function,
            ref arguments,
        } => todo!("function = `{:?}`", function),
        VdBsqExprData::FoldingSeparatedList {
            leader,
            ref followers,
        } => match followers[0].0.separator() {
            VdMirBaseFoldingSeparator::CommRingAdd => merge_sum_construction(lopd, ropd, elr, hc),
            VdMirBaseFoldingSeparator::CommRingMul => {
                merge_product_construction(lopd, ropd, elr, hc)
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

fn merge_nonzero_literal_construction<'db, 'sess>(
    lopd: VdBsqExpr<'sess>,
    ropd: VdBsqExpr<'sess>,
    ropd_literal: VdLiteral,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdMirTermDerivationConstruction {
    match *lopd.data() {
        VdBsqExprData::Literal(lopd) => VdMirTermDerivationConstruction::LiteralAddLiteral {
            lopd,
            ropd: ropd_literal,
        },
        VdBsqExprData::Variable(lx_math_letter, arena_idx) => {
            VdMirTermDerivationConstruction::AtomAddNonZeroLiteral
        }
        VdBsqExprData::Application {
            function,
            ref arguments,
        } => todo!("function = `{:?}`", function),
        VdBsqExprData::FoldingSeparatedList {
            leader,
            ref followers,
        } => match followers[0].0.separator() {
            VdMirBaseFoldingSeparator::CommRingAdd => {
                let (a, _, b) = lopd.split_add(elr, hc);
                let c = ropd;
                let a_add_c = derive_add(a, c, elr, hc);
                let a_add_c_derived_add_b = derive_add(a_add_c.derived(), b, elr, hc);
                let a_ty = a.ty();
                let b_ty = b.ty();
                let c_ty = c.ty();
                let ab_ty = lopd.ty();
                let ac_ty = a_add_c.expr().ty();
                let abc_ty = a_add_c_derived_add_b.expr().ty();
                VdMirTermDerivationConstruction::SumAddLiteral {
                    a_add_c_derivation: a_add_c.derivation(),
                    a_add_c_derived_add_b_derivation: a_add_c_derived_add_b.derivation(),
                    a_add_b_add_coercion: VdMirSeparatorCoercion::new_comm_ring_add(ab_ty, abc_ty),
                    a_ab_abc_coercion_triangle: VdMirCoercionTriangle::new(a_ty, ab_ty, abc_ty),
                    b_ab_abc_coercion_triangle: VdMirCoercionTriangle::new(b_ty, ab_ty, abc_ty),
                    ac_eq_coercion: VdMirSeparatorCoercion::new_eq(ac_ty, abc_ty),
                    ac_add_coercion: VdMirSeparatorCoercion::new_comm_ring_add(ac_ty, abc_ty),
                    a_ac_abc_coercion_triangle: VdMirCoercionTriangle::new(a_ty, ac_ty, abc_ty),
                    c_ac_abc_coercion_triangle: VdMirCoercionTriangle::new(c_ty, ac_ty, abc_ty),
                }
            }
            VdMirBaseFoldingSeparator::CommRingMul => {
                VdMirTermDerivationConstruction::ProductAddLiteral
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

// fn merge_atom_construction<'db, 'sess>(
//     lopd: VdBsqExpr<'sess>,
//     ropd: VdBsqExpr<'sess>,
//     elr: &mut VdBsqElaboratorInner<'db, 'sess>,
//     hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
// ) -> VdMirTermDerivationConstruction {
//     match *lopd.data() {
//         VdBsqExprData::Literal(lopd) => {
//             if lopd.is_zero() {
//                 todo!()
//             } else {
//                 VdMirTermDerivationConstruction::NonZeroLiteralAddAtom
//             }
//         }
//         VdBsqExprData::Variable(lx_math_letter, arena_idx) => todo!(),
//         VdBsqExprData::Application {
//             function,
//             ref arguments,
//         } => todo!("function = `{:?}`", function),
//         VdBsqExprData::FoldingSeparatedList { ref followers, .. } => {
//             match followers[0].0.separator() {
//                 VdMirBaseFoldingSeparator::CommRingAdd => {
//                     let (signature, lropd) = *followers.last().unwrap();
//                     let (a, _, b) = lopd
//                         .split_folding_separated_list(VdMirBaseFoldingSeparator::CommRingAdd, elr);
//                     let VdBsqTerm::Comnum(VdBsqComnumTerm::Atom(ropd_term)) = ropd.term() else {
//                         unreachable!()
//                     };
//                     let c = ropd;
//                     match lropd_stem.cmp(&VdBsqProductStem::Atom(ropd_term)) {
//                         std::cmp::Ordering::Less => todo!(),
//                         std::cmp::Ordering::Equal => todo!(),
//                         std::cmp::Ordering::Greater => {
//                             let a_add_c = merge(a, c, elr, hc);
//                             let term_ac_add_b = merge(a_add_c.expr(), b, elr, hc);
//                             todo!("reduce to the case of merge product")
//                             // VdMirTermDerivationConstruction::SumNfAddProductGreater {
//                             //     a_add_c_nf: a_add_c.derivation(),
//                             //     term_ac_add_b_nf: term_ac_add_b.derivation(),
//                             // }
//                         }
//                     }
//                 }
//                 VdMirBaseFoldingSeparator::CommRingMul => todo!(),
//                 VdMirBaseFoldingSeparator::SetTimes => todo!(),
//                 VdMirBaseFoldingSeparator::TensorOtimes => todo!(),
//             }
//         }
//         VdBsqExprData::ChainingSeparatedList {
//             leader,
//             ref followers,
//             joined_signature,
//         } => todo!(),
//         VdBsqExprData::ItemPath(vd_item_path) => todo!(),
//     }
// }

fn merge_product_construction<'db, 'sess>(
    lopd: VdBsqExpr<'sess>,
    ropd: VdBsqExpr<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdMirTermDerivationConstruction {
    let ropd_stem = product_stem(ropd);
    match lopd.data() {
        VdBsqExprData::Literal(literal) => {
            assert!(!literal.is_zero());
            VdMirTermDerivationConstruction::Reflection
        }
        VdBsqExprData::Variable(..) => {
            let lopd_stem: VdBsqProductStem = match lopd.term() {
                VdBsqTerm::Litnum(lopd) => unreachable!(),
                VdBsqTerm::Comnum(lopd) => match lopd {
                    VdBsqComnumTerm::Atom(lopd) => lopd.into(),
                    VdBsqComnumTerm::Sum(lopd) => unreachable!(),
                    VdBsqComnumTerm::Product(lopd) => unreachable!(),
                },
                VdBsqTerm::Prop(lopd) => todo!(),
                VdBsqTerm::Set(lopd) => todo!(),
            };
            match lopd_stem.cmp(&ropd_stem) {
                std::cmp::Ordering::Less => VdMirTermDerivationConstruction::AtomAddProductLess,
                std::cmp::Ordering::Equal => todo!(),
                std::cmp::Ordering::Greater => {
                    VdMirTermDerivationConstruction::AtomAddProductGreater
                }
            }
        }
        VdBsqExprData::Application {
            function,
            arguments,
        } => todo!(),
        VdBsqExprData::FoldingSeparatedList { leader, followers } => {
            let fst_signature = &followers[0].0;
            match fst_signature.separator() {
                VdMirBaseFoldingSeparator::CommRingAdd => {
                    let last_follower = followers.last().unwrap().1;
                    match product_stem(last_follower).cmp(&ropd_stem) {
                        std::cmp::Ordering::Less => VdMirTermDerivationConstruction::Reflection,
                        std::cmp::Ordering::Equal => todo!(),
                        std::cmp::Ordering::Greater => {
                            let (a, _, b) = lopd.split_folding_separated_list(
                                VdMirBaseFoldingSeparator::CommRingAdd,
                                elr,
                            );
                            let c = ropd;
                            let a_add_c_nf = derive_add(a, c, elr, hc);
                            let term_ac_add_b_nf = derive_add(a_add_c_nf.derived(), b, elr, hc);
                            VdMirTermDerivationConstruction::SumAddProductGreater {
                                a_add_c_nf: a_add_c_nf.derivation(),
                                term_ac_add_b_nf: term_ac_add_b_nf.derivation(),
                            }
                        }
                    }
                }
                VdMirBaseFoldingSeparator::CommRingMul => {
                    let lopd_stem = product_stem(lopd);
                    let ropd_stem = product_stem(ropd);
                    match lopd_stem.cmp(&ropd_stem) {
                        std::cmp::Ordering::Less => {
                            VdMirTermDerivationConstruction::ProductAddProductLess {
                                zero_add_a_add_coercion: VdMirSeparatorCoercion::new_comm_ring_add(
                                    lopd.ty(),
                                    fst_signature.item_ty(),
                                ),
                            }
                        }
                        std::cmp::Ordering::Equal => todo!(),
                        std::cmp::Ordering::Greater => {
                            VdMirTermDerivationConstruction::ProductAddProductGreater {
                                zero_add_b_add_coercion: VdMirSeparatorCoercion::new_comm_ring_add(
                                    ropd.ty(),
                                    fst_signature.item_ty(),
                                ),
                            }
                        }
                    }
                }
                VdMirBaseFoldingSeparator::SetTimes => todo!(),
                VdMirBaseFoldingSeparator::TensorOtimes => todo!(),
            }
        }
        VdBsqExprData::ChainingSeparatedList {
            leader,
            followers,
            joined_signature,
        } => todo!(),
        VdBsqExprData::ItemPath(vd_item_path) => todo!(),
    }
}

fn product_stem<'sess>(product: VdBsqExpr<'sess>) -> VdBsqProductStem<'sess> {
    match product.term() {
        VdBsqTerm::Litnum(vd_bsq_litnum_term) => todo!(),
        VdBsqTerm::Comnum(lropd) => match lropd {
            VdBsqComnumTerm::Atom(lropd) => lropd.into(),
            VdBsqComnumTerm::Sum(_) => todo!(),
            VdBsqComnumTerm::Product(lropd) => lropd.stem(),
        },
        VdBsqTerm::Prop(vd_bsq_prop_term) => todo!(),
        VdBsqTerm::Set(vd_bsq_set_term) => todo!(),
    }
}

fn merge_sum_construction<'db, 'sess>(
    lopd: VdBsqExpr<'sess>,
    ropd: VdBsqExpr<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdMirTermDerivationConstruction {
    let a = lopd;
    let (b, _, c) = ropd.split_folding_separated_list(VdMirBaseFoldingSeparator::CommRingAdd, elr);
    let a_add_b_derived = derive_add(a, b, elr, hc);
    let a_add_b_derived_add_c_derived = derive_add(a_add_b_derived.derived(), c, elr, hc);
    VdMirTermDerivationConstruction::AddSum {
        a_add_b_derivation: a_add_b_derived.derivation(),
        a_add_b_derived_add_c_derivation: a_add_b_derived_add_c_derived.derivation(),
    }
}
