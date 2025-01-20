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
            if let Some(construction) = try_trivial_literal_mul(leader, follower) {
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

fn try_trivial_literal_mul<'sess>(
    lopd: VdBsqExpr<'sess>,
    ropd: VdBsqExpr<'sess>,
) -> Option<VdMirTermDerivationConstruction> {
    if let (&VdBsqExprData::Literal(leader), &VdBsqExprData::Literal(follower)) =
        (lopd.data(), ropd.data())
    {
        return Some(VdMirTermDerivationConstruction::LiteralMul);
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
    if let Some(construction) = try_trivial_literal_mul(lopd, ropd) {
        return construction;
    }
    match *ropd.data() {
        VdBsqExprData::Literal(literal) => merge_literal(lopd, literal, elr, hc),
        VdBsqExprData::Variable(lx_math_letter, local_defn) => {
            merge_atom_construction(lopd, ropd, elr, hc)
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

fn merge_atom_construction<'db, 'sess>(
    lopd: VdBsqExpr<'sess>,
    ropd: VdBsqExpr<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdMirTermDerivationConstruction {
    match *lopd.data() {
        VdBsqExprData::Literal(literal) => {
            if literal.is_one() {
                VdMirTermDerivationConstruction::OneMulAtom
            } else {
                VdMirTermDerivationConstruction::NonOneLiteralMulAtom
            }
        }
        VdBsqExprData::Variable(lx_math_letter, arena_idx) => todo!(),
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
