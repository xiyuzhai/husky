use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct VdBsqExprDerived<'sess> {
    derivation: VdMirTermDerivationIdx,
    derived: VdBsqExpr<'sess>,
}

impl<'sess> std::ops::Deref for VdBsqExprDerived<'sess> {
    type Target = VdBsqExpr<'sess>;

    fn deref(&self) -> &Self::Target {
        &self.derived
    }
}

impl<'db, 'sess> VdBsqExprDerived<'sess> {
    pub(super) fn new(
        derivation: VdMirTermDerivationIdx,
        expr: VdBsqExpr<'sess>,
        elr: &mut VdBsqElaboratorInner<'db, 'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> Self {
        Self {
            derivation,
            derived: expr.term().expr(elr, hc),
        }
    }

    pub(super) fn new_override(
        derivation: VdMirTermDerivationIdx,
        derived: VdBsqExpr<'sess>,
        elr: &mut VdBsqElaboratorInner<'db, 'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> Self {
        Self {
            derivation,
            derived,
        }
    }
}

impl<'sess> VdBsqExprDerived<'sess> {
    pub(super) fn derived(self) -> VdBsqExpr<'sess> {
        self.derived
    }

    pub(super) fn derivation(self) -> VdMirTermDerivationIdx {
        self.derivation
    }
}
