use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct VdBsqExprNf<'sess> {
    derivation: VdMirTermDerivationIdx,
    expr: VdBsqExprFld<'sess>,
}

impl<'sess> std::ops::Deref for VdBsqExprNf<'sess> {
    type Target = VdBsqExprFld<'sess>;

    fn deref(&self) -> &Self::Target {
        &self.expr
    }
}

impl<'sess> VdBsqExprNf<'sess> {
    pub(super) fn new(derivation: VdMirTermDerivationIdx, expr: VdBsqExprFld<'sess>) -> Self {
        Self { derivation, expr }
    }
}

impl<'sess> VdBsqExprNf<'sess> {
    pub(super) fn expr(self) -> VdBsqExprFld<'sess> {
        self.expr
    }

    pub(super) fn derivation(self) -> VdMirTermDerivationIdx {
        self.derivation
    }
}
