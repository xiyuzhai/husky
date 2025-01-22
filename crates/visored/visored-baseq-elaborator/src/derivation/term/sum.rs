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
            if let Some(construction) = try_trivial_literal_add(leader, follower) {
                return construction;
            }
        }
        let (lopd, _, ropd) = self.split_folding_separated_list(leader, followers);
        let lopd = lopd.normalize(self, hc);
        let ropd = ropd.normalize(self, hc);
        VdMirTermDerivationConstruction::AddEq {
            lopd: lopd.derivation(),
            ropd: ropd.derivation(),
            merge: merge_nf_add_nf(lopd, ropd, self, hc).derivation(),
        }
    }
}

fn try_trivial_literal_add<'sess>(
    lopd: VdBsqExpr<'sess>,
    ropd: VdBsqExpr<'sess>,
) -> Option<VdMirTermDerivationConstruction> {
    if let (&VdBsqExprData::Literal(lopd), &VdBsqExprData::Literal(ropd)) =
        (lopd.data(), ropd.data())
    {
        return Some(VdMirTermDerivationConstruction::LiteralAddLiteral { lopd, ropd });
    }
    None
}

fn merge_nf_add_nf<'db, 'sess>(
    lopd: VdBsqExprNf<'sess>,
    ropd: VdBsqExprNf<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdBsqExprNf<'sess> {
    let construction = merge_nf_add_nf_construction(lopd, ropd, elr, hc);
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
    let expr = elr.mk_add(lopd.expr(), ropd.expr(), hc);
    let prop = elr.transcribe_expr_term_derivation_prop(expr, hc);
    let derivation = hc.alloc_term_derivation(prop, construction);
    VdBsqExprNf::new(derivation, expr, elr, hc)
}

fn merge_nf_add_nf_construction<'db, 'sess>(
    lopd: VdBsqExprNf<'sess>,
    ropd: VdBsqExprNf<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdMirTermDerivationConstruction {
    if let Some(construction) = try_trivial_literal_add(lopd.expr(), ropd.expr()) {
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
            merge_nf_add_atom_construction(lopd, ropd, elr, hc)
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
                merge_nf_add_product_construction(lopd, ropd, elr, hc)
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
    lopd: VdBsqExprNf<'sess>,
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

fn merge_nf_add_atom_construction<'db, 'sess>(
    lopd: VdBsqExprNf<'sess>,
    ropd: VdBsqExprNf<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdMirTermDerivationConstruction {
    match *lopd.data() {
        VdBsqExprData::Literal(lopd) => {
            if lopd.is_zero() {
                todo!()
            } else {
                VdMirTermDerivationConstruction::NonZeroLiteralAddAtom
            }
        }
        VdBsqExprData::Variable(lx_math_letter, arena_idx) => todo!(),
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

fn merge_nf_add_product_construction<'db, 'sess>(
    lopd: VdBsqExprNf<'sess>,
    ropd: VdBsqExprNf<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdMirTermDerivationConstruction {
    let VdBsqTerm::Comnum(VdBsqComnumTerm::Product(product)) = ropd.term() else {
        unreachable!()
    };
    match lopd.term() {
        VdBsqTerm::Litnum(_) => todo!(),
        VdBsqTerm::Comnum(lopd) => match lopd {
            VdBsqComnumTerm::Atom(lopd) => VdMirTermDerivationConstruction::AtomAddProduct {
                comparison: VdBsqProductStem::Atom(lopd).cmp(&product.stem()),
            },
            VdBsqComnumTerm::Sum(vd_bsq_sum_term) => todo!(),
            VdBsqComnumTerm::Product(vd_bsq_product_term) => todo!(),
        },
        VdBsqTerm::Prop(vd_bsq_prop_term) => todo!(),
        VdBsqTerm::Set(vd_bsq_set_term) => todo!(),
    }
}
