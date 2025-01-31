use super::*;

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess> {
    pub(super) fn transcribe_neg_term_derivation_construction(
        &mut self,
        opd: VdBsqExpr<'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirTermDerivationConstruction {
        match *opd.data() {
            VdBsqExprData::Literal(vd_literal) => VdMirTermDerivationConstruction::NegLiteral,
            VdBsqExprData::Variable(lx_math_letter, arena_idx) => {
                VdMirTermDerivationConstruction::NegAtom
            }
            VdBsqExprData::ItemPath(vd_item_path) => todo!(),
            _ => {
                let opd = opd.normalize(self, hc);
                let minus_opd_nf_nf = neg_derived(opd.derived(), self, hc);
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

fn neg_derived<'db, 'sess>(
    opd: VdBsqExpr<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdBsqExprDerived<'sess> {
    let (construction, derived) = neg_nf_construction_and_derived(opd, elr, hc);
    let expr = elr.mk_neg(opd, hc);
    VdBsqExprDerived::new(expr, derived, construction, elr, hc)
}

fn neg_nf_construction_and_derived<'db, 'sess>(
    opd: VdBsqExpr<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> (VdMirTermDerivationConstruction, Option<VdBsqExpr<'sess>>) {
    if let Some(construction) = try_trivial_construction(opd, elr, hc) {
        return (construction, None);
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
            VdMirBaseFoldingSeparator::CommRingAdd => {
                neg_sum_construction_and_derived(opd, elr, hc)
            }
            VdMirBaseFoldingSeparator::CommRingMul => (
                neg_product_construction(opd, elr, hc),
                Some(elr.mk_neg(opd, hc).term().expr(elr, hc)),
            ),
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

fn neg_sum_construction_and_derived<'db, 'sess>(
    opd: VdBsqExpr<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> (VdMirTermDerivationConstruction, Option<VdBsqExpr<'sess>>) {
    let (a, _, b) = opd.split_folding_separated_list(VdMirBaseFoldingSeparator::CommRingAdd, elr);
    let neg_a_nf = neg_derived(a, elr, hc);
    let neg_b_nf = neg_derived(b, elr, hc);
    let derived = elr.mk_add(*neg_a_nf, *neg_b_nf, hc);
    (
        VdMirTermDerivationConstruction::NegSum {
            neg_a_nf: neg_a_nf.derivation(),
            neg_b_nf: neg_b_nf.derivation(),
        },
        Some(derived),
    )
}

fn neg_product_construction<'db, 'sess>(
    opd: VdBsqExpr<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdMirTermDerivationConstruction {
    VdMirTermDerivationConstruction::NegProduct
}
