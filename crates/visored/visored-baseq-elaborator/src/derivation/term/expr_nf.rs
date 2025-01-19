use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct VdBsqExprNf<'sess> {
    derivation: VdMirTermDerivationIdx,
    expr: VdBsqExpr<'sess>,
}

impl<'sess> std::ops::Deref for VdBsqExprNf<'sess> {
    type Target = VdBsqExpr<'sess>;

    fn deref(&self) -> &Self::Target {
        &self.expr
    }
}

impl<'db, 'sess> VdBsqExprNf<'sess> {
    pub(super) fn new(
        derivation: VdMirTermDerivationIdx,
        expr: VdBsqExpr<'sess>,
        elr: &mut VdBsqElaboratorInner<'db, 'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> Self {
        Self {
            derivation,
            expr: expr.term().expr(elr, hc),
        }
    }
}

impl<'sess> VdBsqExprNf<'sess> {
    pub(super) fn expr(self) -> VdBsqExpr<'sess> {
        self.expr
    }

    pub(super) fn derivation(self) -> VdMirTermDerivationIdx {
        self.derivation
    }
}
