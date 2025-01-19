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

impl<'sess> VdBsqExprNf<'sess> {
    pub(super) fn new(derivation: VdMirTermDerivationIdx, expr: VdBsqExpr<'sess>) -> Self {
        Self { derivation, expr }
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
