use crate::term::{
    comnum::{product::VdBsqProductStem, VdBsqComnumTerm},
    VdBsqTerm,
};

use super::*;
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
        let (lopd, _, ropd) = self.split_folding_separated_list(leader, followers);
        let lopd = lopd.normalize(self, hc);
        let ropd = ropd.normalize(self, hc);
        VdMirTermDerivationConstruction::AddEq {
            lopd: lopd.derivation(),
            ropd: ropd.derivation(),
            merge: merge(*lopd, *ropd, self, hc).derivation(),
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

fn merge<'db, 'sess>(
    lopd: VdBsqExpr<'sess>,
    ropd: VdBsqExpr<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdBsqExprNf<'sess> {
    let construction = merge_construction(lopd, ropd, elr, hc);
    match construction {
        VdMirTermDerivationConstruction::LiteralAddLiteral {
            lopd: lopd_lit,
            ropd: ropd_lit,
        } => {
            use husky_print_utils::p;
            p!(lopd, ropd, lopd_lit, ropd_lit);
            todo!()
        }
        _ => (),
    }
    let expr = elr.mk_add(lopd, ropd, hc);
    let prop = elr.transcribe_expr_term_derivation_prop(expr, hc);
    let derivation = hc.alloc_term_derivation(prop, construction);
    VdBsqExprNf::new(derivation, expr, elr, hc)
}

fn merge_construction<'db, 'sess>(
    lopd: VdBsqExpr<'sess>,
    ropd: VdBsqExpr<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdMirTermDerivationConstruction {
    if let Some(construction) = try_trivial_construction(lopd, ropd, elr, hc) {
        return construction;
    }
    match *ropd.data() {
        VdBsqExprData::Literal(literal) => {
            if literal.is_zero() {
                VdMirTermDerivationConstruction::NfAddZero
            } else {
                merge_nf_add_nonzero_literal_construction(lopd, literal, elr, hc)
            }
        }
        VdBsqExprData::Variable(lx_math_letter, arena_idx) => {
            let ropd = elr.mk_mul(elr.mk_i128(1), elr.mk_pow(ropd, elr.mk_i128(1), hc), hc);
            let add_product_nf = merge(lopd, ropd, elr, hc).derivation();
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
            VdMirBaseFoldingSeparator::CommRingAdd => todo!(),
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

fn merge_nf_add_nonzero_literal_construction<'db, 'sess>(
    lopd: VdBsqExpr<'sess>,
    ropd: VdLiteral,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdMirTermDerivationConstruction {
    match *lopd.data() {
        VdBsqExprData::Literal(lopd) => {
            VdMirTermDerivationConstruction::LiteralAddLiteral { lopd, ropd }
        }
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
        } => todo!(),
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
            VdMirTermDerivationConstruction::AtomAddProduct {
                comparison: lopd_stem.cmp(&ropd_stem),
            }
        }
        VdBsqExprData::Application {
            function,
            arguments,
        } => todo!(),
        VdBsqExprData::FoldingSeparatedList { leader, followers } => {
            match followers[0].0.separator() {
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
                            let a_add_c_nf = merge(a, c, elr, hc);
                            let term_ac_add_b_nf = merge(a_add_c_nf.expr(), b, elr, hc);
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
                            VdMirTermDerivationConstruction::ProductAddProductLess
                        }
                        std::cmp::Ordering::Equal => todo!(),
                        std::cmp::Ordering::Greater => {
                            VdMirTermDerivationConstruction::ProductAddProductGreater
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
