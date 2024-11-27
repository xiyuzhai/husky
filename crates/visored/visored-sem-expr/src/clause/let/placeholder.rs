use super::*;
use crate::pattern::VdSemPattern;
use visored_syn_expr::clause::r#let::placeholder::{
    VdSynLetClausePlaceholderType, VdSynLetPlaceholderResolution,
};
use visored_term::{term::VdTerm, ty::VdType};

#[derive(Debug, PartialEq, Eq)]
pub struct VdSemLetPlaceholderDispatch {
    pattern: VdSemPattern,
    ty_repr: VdSemLetClausePlaceholderTypeRepr,
    ty: VdType,
}

#[enum_class::from_variants]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VdSemLetClausePlaceholderTypeRepr {
    Expr(VdSemExprIdx),
}

impl VdSemLetPlaceholderDispatch {
    pub fn pattern(&self) -> &VdSemPattern {
        &self.pattern
    }

    pub fn ty_repr(&self) -> &VdSemLetClausePlaceholderTypeRepr {
        &self.ty_repr
    }

    pub fn ty(&self) -> VdType {
        self.ty
    }
}

impl ToVdSem<VdSemLetPlaceholderDispatch> for &VdSynLetPlaceholderResolution {
    fn to_vd_sem(self, builder: &mut VdSemExprBuilder) -> VdSemLetPlaceholderDispatch {
        let pattern = self.pattern().to_vd_sem(builder);
        let ty_repr = self.ty().to_vd_sem(builder);
        let ty_term = builder.infer_pattern_ty_term(ty_repr);
        let ty = ty_term.to_ty();
        builder.infer_pattern_symbol_tys(&pattern, ty);
        VdSemLetPlaceholderDispatch {
            pattern,
            ty_repr,
            ty,
        }
    }
}

impl ToVdSem<VdSemLetClausePlaceholderTypeRepr> for VdSynLetClausePlaceholderType {
    fn to_vd_sem(self, builder: &mut VdSemExprBuilder) -> VdSemLetClausePlaceholderTypeRepr {
        match self {
            VdSynLetClausePlaceholderType::Expr(expr) => {
                VdSemLetClausePlaceholderTypeRepr::Expr(expr.to_vd_sem(builder))
            }
        }
    }
}

impl<'db> VdSemExprBuilder<'db> {
    fn infer_pattern_ty_term(&mut self, ty: VdSemLetClausePlaceholderTypeRepr) -> VdTerm {
        match ty {
            VdSemLetClausePlaceholderTypeRepr::Expr(expr) => self.infer_expr_term(expr),
        }
    }
}
