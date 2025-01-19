use crate::foundations::opr::separator::relation::comparison::VdBsqComparisonOpr;
use smallvec::*;
use visored_opr::separator::VdBaseSeparator;

use super::*;

#[floated]
pub struct VdBsqNumRelation<'sess> {
    pub lhs_minus_rhs: VdBsqNumTerm<'sess>,
    pub opr: VdBsqComparisonOpr,
}

impl<'sess> VdBsqNumRelation<'sess> {
    pub fn new(
        lhs: VdBsqNumTerm<'sess>,
        kind: VdBsqComparisonOpr,
        rhs: VdBsqNumTerm<'sess>,
        db: &'sess FloaterDb,
    ) -> VdBsqPropTerm<'sess> {
        use husky_print_utils::*;
        let lhs_minus_rhs = lhs.sub(rhs, db);
        match lhs_minus_rhs {
            VdBsqNumTerm::Litnum(term) => return VdBsqPropTerm::Trivial(term.cmp_with_zero(kind)),
            VdBsqNumTerm::Comnum(term) => (),
        }
        Self::new_inner(lhs_minus_rhs, kind, db).into()
    }
}

impl<'sess> VdBsqPropTerm<'sess> {
    pub fn new_num_relationship(
        lhs: VdBsqNumTerm<'sess>,
        kind: VdBsqComparisonOpr,
        rhs: VdBsqNumTerm<'sess>,
        db: &'sess FloaterDb,
    ) -> Self {
        VdBsqNumRelation::new(lhs, kind, rhs, db)
    }
}

impl<'sess> VdBsqTerm<'sess> {
    pub fn new_num_relationship(
        lhs: VdBsqNumTerm<'sess>,
        kind: VdBsqComparisonOpr,
        rhs: VdBsqNumTerm<'sess>,
        db: &'sess FloaterDb,
    ) -> Self {
        VdBsqPropTerm::new_num_relationship(lhs, kind, rhs, db).into()
    }
}

impl<'sess> std::fmt::Debug for VdBsqNumRelation<'sess> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("NumRelationshipPropTerm(`")?;
        self.show_fmt(VdPrecedenceRange::Any, f)?;
        f.write_str("`)")
    }
}

impl<'sess> VdBsqNumRelation<'sess> {
    pub fn show_fmt(
        self,
        precedence_range: VdPrecedenceRange,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        self.lhs_minus_rhs().show_fmt(precedence_range, f)?;
        f.write_str(" ")?;
        match self.opr() {
            VdBsqComparisonOpr::EQ => f.write_str("="),
            VdBsqComparisonOpr::NE => f.write_str("≠"),
            VdBsqComparisonOpr::LT => f.write_str("<"),
            VdBsqComparisonOpr::GT => f.write_str(">"),
            VdBsqComparisonOpr::LE => f.write_str("≤"),
            VdBsqComparisonOpr::GE => f.write_str("≥"),
        }?;
        f.write_str(" 0")
    }
}

impl<'db, 'sess> VdBsqNumRelation<'sess> {
    pub(crate) fn expr(
        self,
        elr: &VdBsqElaboratorInner<'db, 'sess>,
        hc: &VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdBsqExpr<'sess> {
        let lhs_minus_rhs = self.lhs_minus_rhs().expr(elr, hc);
        let lhs_minus_rhs_ty = lhs_minus_rhs.ty();
        let signature = hc.infer_base_comparison_separator_signature(
            lhs_minus_rhs_ty,
            self.opr().into(),
            lhs_minus_rhs_ty,
        );
        let zero = elr.mk_zero();
        elr.mk_expr(
            VdBsqExprData::ChainingSeparatedList {
                leader: lhs_minus_rhs,
                followers: smallvec![(signature.into(), zero)],
                joined_signature: None,
            },
            signature.expr_ty(),
        )
    }
}
