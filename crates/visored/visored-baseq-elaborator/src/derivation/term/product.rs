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
            merge: merge(lopd.expr(), ropd.expr(), self, hc).derivation(),
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
) -> VdBsqExprNf<'sess> {
    let construction = merge_construction(lopd, ropd, elr, hc);
    let expr = elr.mk_mul(lopd, ropd, hc);
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
        VdBsqExprData::Literal(literal) => merge_literal(lopd, literal, elr, hc),
        VdBsqExprData::FoldingSeparatedList { ref followers, .. }
            if followers[0].0.separator() == VdMirBaseFoldingSeparator::COMM_RING_MUL =>
        {
            let (rlopd, rsignature, rropd) = ropd.split_mul(elr, hc);
            let merge_rlopd_nf = merge(lopd, rlopd, elr, hc);
            let merge_rropd_nf = merge(merge_rlopd_nf.expr(), rropd, elr, hc);
            VdMirTermDerivationConstruction::MulAssoc {
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
    match *lopd.data() {
        VdBsqExprData::Literal(literal) => {
            assert!(!literal.is_one());
            VdMirTermDerivationConstruction::Reflection
        }
        _ => todo!(),
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
