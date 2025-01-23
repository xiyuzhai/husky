use super::*;

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub(super) fn transcribe_neg_term_derivation_construction(
        &mut self,
        opd: VdBsqExpr<'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirTermDerivationConstruction {
        match *opd.data() {
            VdBsqExprData::Literal(vd_literal) => VdMirTermDerivationConstruction::NegLiteral,
            VdBsqExprData::Variable(lx_math_letter, arena_idx) => todo!(),
            VdBsqExprData::ItemPath(vd_item_path) => todo!(),
            _ => {
                let opd = opd.normalize(self, hc);
                let minus_opd_nf_nf = neg_nf(opd.expr(), self, hc);
                VdMirTermDerivationConstruction::NegEq {
                    opd_nf: opd.derivation(),
                    minus_opd_nf_nf: minus_opd_nf_nf.derivation(),
                }
            }
        }
    }
}

fn try_trivial_construction<'db, 'sess>(
    opd: VdBsqExpr<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> Option<VdMirTermDerivationConstruction> {
    match *opd.data() {
        VdBsqExprData::Literal(vd_literal) => Some(VdMirTermDerivationConstruction::NegLiteral),
        VdBsqExprData::Variable(lx_math_letter, arena_idx) => todo!(),
        VdBsqExprData::ItemPath(vd_item_path) => todo!(),
        _ => None,
    }
}

fn neg_nf<'db, 'sess>(
    opd: VdBsqExpr<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdBsqExprNf<'sess> {
    let construction = neg_nf_construction(opd, elr, hc);
    let expr = elr.mk_neg(opd, hc);
    let prop = elr.transcribe_expr_term_derivation_prop(expr, hc);
    let derivation = hc.alloc_term_derivation(prop, construction);
    VdBsqExprNf::new(derivation, expr, elr, hc)
}

fn neg_nf_construction<'db, 'sess>(
    opd: VdBsqExpr<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdMirTermDerivationConstruction {
    if let Some(construction) = try_trivial_construction(opd, elr, hc) {
        return construction;
    }
    match *opd.data() {
        VdBsqExprData::Literal(vd_literal) => todo!(),
        VdBsqExprData::Variable(lx_math_letter, arena_idx) => todo!(),
        VdBsqExprData::Application {
            function,
            ref arguments,
        } => todo!(),
        VdBsqExprData::FoldingSeparatedList {
            leader,
            ref followers,
        } => match followers[0].0.separator() {
            VdMirBaseFoldingSeparator::CommRingAdd => neg_sum_nf(opd, elr, hc),
            VdMirBaseFoldingSeparator::CommRingMul => neg_product_nf(opd, elr, hc),
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

fn neg_sum_nf<'db, 'sess>(
    opd: VdBsqExpr<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdMirTermDerivationConstruction {
    let (a, _, b) = opd.split_folding_separated_list(VdMirBaseFoldingSeparator::CommRingAdd, elr);
    let neg_a_nf = neg_nf(a, elr, hc);
    let neg_b_nf = neg_nf(b, elr, hc);
    assert!(!a.is_zero());
    p!(opd, a, b);
    todo!();
    VdMirTermDerivationConstruction::NegSum {
        neg_a_nf: neg_a_nf.derivation(),
        neg_b_nf: neg_b_nf.derivation(),
    }
}

fn neg_product_nf<'db, 'sess>(
    opd: VdBsqExpr<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdMirTermDerivationConstruction {
    VdMirTermDerivationConstruction::NegProduct
}
