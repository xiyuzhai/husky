use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VdBsqExprDerived<'sess> {
    expr: VdBsqExpr<'sess>,
    derived: VdBsqExpr<'sess>,
    derivation: VdMirTermDerivationIdx,
}

impl<'sess> std::ops::Deref for VdBsqExprDerived<'sess> {
    type Target = VdBsqExpr<'sess>;

    fn deref(&self) -> &Self::Target {
        &self.derived
    }
}

impl<'db, 'sess> VdBsqExprDerived<'sess> {
    pub(super) fn new(
        expr: VdBsqExpr<'sess>,
        derived: Option<VdBsqExpr<'sess>>,
        construction: VdMirTermDerivationConstruction,
        elr: &mut VdBsqElaboratorInner<'db, 'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> Self {
        let derived = derived.unwrap_or_else(|| expr.term().expr(elr, hc));
        let prop = transcribe_expr_derivation_prop(expr, derived, elr, hc);
        let derivation = hc.alloc_term_derivation(prop, construction);
        Self {
            expr,
            derived,
            derivation,
        }
    }
}

fn transcribe_expr_derivation_prop<'db, 'sess>(
    expr: VdBsqExpr<'sess>,
    derived: VdBsqExpr<'sess>,
    elr: &mut VdBsqElaboratorInner<'db, 'sess>,
    hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
) -> VdMirExprIdx {
    let term = expr.term();
    let (expr_transcription, expr_ty) = expr.transcribe_with_ty(None, elr, hc);
    let (derived_transcription, derived_ty) = derived.transcribe_with_ty(None, elr, hc);
    let signature = hc.infer_equivalence_signature(expr_ty, derived_ty);
    let prop_expr_data = VdMirExprData::ChainingSeparatedList {
        leader: expr_transcription,
        followers: smallvec![(signature, derived_transcription)],
        joined_signature: None,
    };
    let prop_expr_ty = elr.ty_menu().prop;
    hc.mk_expr(VdMirExprEntry::new(prop_expr_data, prop_expr_ty, None))
}

impl<'sess> VdBsqExprDerived<'sess> {
    pub(super) fn derived(self) -> VdBsqExpr<'sess> {
        self.derived
    }

    pub(super) fn derivation(self) -> VdMirTermDerivationIdx {
        self.derivation
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VdBsqExprNormalized<'sess>(VdBsqExprDerived<'sess>);

impl<'sess> std::ops::Deref for VdBsqExprNormalized<'sess> {
    type Target = VdBsqExprDerived<'sess>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'db, 'sess> VdBsqExprNormalized<'sess> {
    pub(super) fn new(
        expr: VdBsqExpr<'sess>,
        construction: VdMirTermDerivationConstruction,
        elr: &mut VdBsqElaboratorInner<'db, 'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> Self {
        Self(VdBsqExprDerived::new(expr, None, construction, elr, hc))
    }
}
