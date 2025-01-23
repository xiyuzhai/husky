use crate::term::{
    comnum::{product::VdBsqProductStem, VdBsqComnumTerm},
    num::VdBsqNumTerm,
    VdBsqTerm,
};

use super::*;
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
            merge: merge(lopd.derived(), ropd.derived(), self, hc).derivation(),
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

fn merge<'db, 'sess>(
    lopd: VdBsqExpr<'sess>,
    ropd: VdBsqExpr<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdBsqExprDerived<'sess> {
    let construction = merge_construction(lopd, ropd, elr, hc);
    let expr = elr.mk_mul(lopd, ropd, hc);
    let prop = elr.transcribe_expr_term_derivation_prop(expr, hc);
    let derivation = hc.alloc_term_derivation(prop, construction);
    VdBsqExprDerived::new_normalized(derivation, expr, elr, hc)
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
        VdBsqExprData::Literal(literal) => merge_literal(lopd, literal, elr, hc),
        VdBsqExprData::FoldingSeparatedList { ref followers, .. }
            if followers[0].0.separator() == VdMirBaseFoldingSeparator::COMM_RING_MUL =>
        {
            let (rlopd, rsignature, rropd) = ropd.split_mul(elr, hc);
            let merge_rlopd_nf = merge(lopd, rlopd, elr, hc);
            let merge_rropd_nf = merge(merge_rlopd_nf.derived(), rropd, elr, hc);
            VdMirTermDerivationConstruction::MulProduct {
                rsignature,
                merge_rlopd_nf: merge_rlopd_nf.derivation(),
                merge_rropd_nf: merge_rropd_nf.derivation(),
            }
        }
        VdBsqExprData::ItemPath(vd_item_path) => todo!(),
        VdBsqExprData::Application {
            function: VdMirFunc::NormalBaseSqrt(_),
            ref arguments,
        } => todo!(),
        VdBsqExprData::Application {
            function: VdMirFunc::Power(_),
            ref arguments,
        } => merge_exponential_construction(lopd, ropd, elr, hc),
        _ => merge_atom_construction(lopd, ropd, elr, hc),
    }
}

fn merge_literal<'db, 'sess>(
    lopd: VdBsqExpr<'sess>,
    literal: VdLiteral,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdMirTermDerivationConstruction {
    match *lopd.data() {
        VdBsqExprData::Literal(leader) => todo!(),
        VdBsqExprData::Variable(lx_math_letter, arena_idx) => {
            VdMirTermDerivationConstruction::AtomMulSwap
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

fn merge_exponential_construction<'db, 'sess>(
    lopd: VdBsqExpr<'sess>,
    ropd: VdBsqExpr<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdMirTermDerivationConstruction {
    let ropd_base = exponential_base(ropd);
    match *lopd.data() {
        VdBsqExprData::Literal(literal) => {
            assert!(!literal.is_one());
            VdMirTermDerivationConstruction::Reflection
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
                    core::cmp::Ordering::Less => {
                        VdMirTermDerivationConstruction::SimpleProductMulExponentialLess
                    }
                    core::cmp::Ordering::Equal => todo!(),
                    core::cmp::Ordering::Greater => {
                        VdMirTermDerivationConstruction::SimpleProductMulExponentialGreater
                    }
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
) -> VdMirTermDerivationConstruction {
    match *lopd.data() {
        VdBsqExprData::Literal(literal) => {
            assert!(!literal.is_one());
            VdMirTermDerivationConstruction::NonOneLiteralMulAtom
        }
        VdBsqExprData::Variable(..) => {
            if lopd == ropd {
                todo!()
            } else {
                VdMirTermDerivationConstruction::AtomMulAtom {
                    comparison: lopd.term().cmp(&ropd.term()),
                }
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
