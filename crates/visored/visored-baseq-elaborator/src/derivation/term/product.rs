use super::*;
use crate::term::{
    comnum::{product::VdBsqProductStem, VdBsqComnumTerm},
    num::VdBsqNumTerm,
    VdBsqTerm,
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
        let (lopd, signature, ropd) = self.split_folding_separated_list(leader, followers);
        let lopd = lopd.normalize(self, hc);
        let ropd = ropd.normalize(self, hc);
        VdMirTermDerivationConstruction::MulEq {
            lopd: lopd.derivation(),
            ropd: ropd.derivation(),
            merge: derive_product(lopd.derived(), ropd.derived(), self, hc).derivation(),
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

pub fn derive_product<'db, 'sess>(
    lopd: VdBsqExpr<'sess>,
    ropd: VdBsqExpr<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdBsqExprDerived<'sess> {
    let derived = derive_product_aux(lopd, ropd, elr, hc);
    rq!(let VdBsqExprData::FoldingSeparatedList {
        leader,
        ref followers,
    } = *derived.data(), derived);
    rq!(let VdBsqExprData::Literal(_) = leader.data(), derived);
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
    rq!(
        let VdBsqExprData::FoldingSeparatedList {
            followers: ref base_followers,
            ..
        } = *pow_args[0].data(), derived);
    rq!(
        base_followers[0].0.separator() == VdMirBaseFoldingSeparator::COMM_RING_ADD,
        derived
    );
    derive_literal_mul_sum(leader, base_followers[0].1, elr, hc)
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
        VdBsqExprData::Literal(_) => derive_mul_literal_construction(lopd, ropd, elr, hc),
        VdBsqExprData::FoldingSeparatedList { ref followers, .. }
            if followers[0].0.separator() == VdMirBaseFoldingSeparator::COMM_RING_MUL =>
        {
            let (rlopd, rsignature, rropd) = ropd.split_mul(elr, hc);
            let merge_rlopd_nf = derive_product_aux(lopd, rlopd, elr, hc);
            let merge_rropd_nf = derive_product_aux(merge_rlopd_nf.derived(), rropd, elr, hc);
            (
                VdMirTermDerivationConstruction::MulProduct {
                    rsignature,
                    merge_rlopd_nf: merge_rlopd_nf.derivation(),
                    merge_rropd_nf: merge_rropd_nf.derivation(),
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
        _ => merge_atom_construction(lopd, ropd, elr, hc),
    }
}

fn derive_mul_literal_construction<'db, 'sess>(
    lopd: VdBsqExpr<'sess>,
    ropd: VdBsqExpr<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> (VdMirTermDerivationConstruction, Option<VdBsqExpr<'sess>>) {
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
            p!(lopd, ropd);
            todo!()
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
            assert!(!literal.is_one());
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
            if is_product_simple(followers) {
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
        _ => {
            p!(lopd, ropd, ropd_base);
            todo!()
        }
    }
}

fn is_product_simple<'sess>(
    followers: &[(VdBaseFoldingSeparatorSignature, VdBsqExpr<'sess>)],
) -> bool {
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

fn merge_atom_construction<'db, 'sess>(
    lopd: VdBsqExpr<'sess>,
    ropd: VdBsqExpr<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> (VdMirTermDerivationConstruction, Option<VdBsqExpr<'sess>>) {
    match *lopd.data() {
        VdBsqExprData::Literal(literal) => {
            assert!(!literal.is_one());
            let derived = todo!();
            (
                VdMirTermDerivationConstruction::NonOneLiteralMulAtom,
                derived,
            )
        }
        VdBsqExprData::Variable(..) => {
            if lopd == ropd {
                let derived = todo!();
                (
                    VdMirTermDerivationConstruction::AtomMulAtom {
                        comparison: lopd.term().cmp(&ropd.term()),
                    },
                    derived,
                )
            } else {
                (
                    VdMirTermDerivationConstruction::AtomMulAtom {
                        comparison: lopd.term().cmp(&ropd.term()),
                    },
                    None,
                )
            }
        }
        VdBsqExprData::Application {
            function,
            ref arguments,
        } => todo!(),
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

fn derive_literal_mul_sum<'db, 'sess>(
    lopd: VdBsqExpr<'sess>,
    ropd: VdBsqExpr<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdBsqExprDerived<'sess> {
    p!(lopd, lopd.data(), ropd);
    todo!()
}
