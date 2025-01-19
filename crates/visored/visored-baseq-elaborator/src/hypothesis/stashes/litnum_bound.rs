use super::*;
use crate::{
    expr::VdBsqExpr,
    foundations::{
        num::VdBsqSign,
        opr::separator::relation::comparison::{
            VdBsqBoundBoundaryKind, VdBsqBoundOpr, VdBsqComparisonOpr,
        },
    },
    hypothesis::{
        stack::VdBsqHypothesisStack,
        stash::{
            upgrade::{IsVdBsqHypothesisUpgradeStashScheme, VdBsqHypothesisUpgradeStash},
            IsVdBsqHypothesisStashScheme,
        },
    },
    term::{
        builder::{product::VdBsqProductBuilder, sum::VdBsqSumBuilder},
        comnum::{sum::VdBsqSumTerm, VdBsqComnumTerm, VdBsqMonomialCoefficients},
        litnum::VdBsqLitnumTerm,
        num::VdBsqNumTerm,
        prop::VdBsqPropTerm,
        VdBsqTerm,
    },
};
use floated_sequential::db::FloaterDb;
use husky_control_flow_utils::require;

pub type VdBsqLitnumBoundStash<'sess> = VdBsqHypothesisUpgradeStash<'sess, VdBsqLitNumBoundScheme>;

pub struct VdBsqLitNumBoundScheme;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VdBsqLitNumBoundKey<'sess> {
    normalized_monomials: VdBsqComnumTerm<'sess>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct VdBsqNormalizedLitNumBound<'sess> {
    litnum: VdBsqLitnumTerm<'sess>,
    boundary_kind: VdBsqBoundBoundaryKind,
}

impl<'sess> VdBsqNormalizedLitNumBound<'sess> {
    pub fn is_upgrade_of(self, other: Self) -> bool {
        self > other
    }
}

#[test]
fn vd_bsq_normalized_litnum_bound_is_upgrade_works() {
    fn t<'sess>(
        slf: VdBsqNormalizedLitNumBound<'sess>,
        other: VdBsqNormalizedLitNumBound<'sess>,
        expected: bool,
    ) {
        assert_eq!(slf.is_upgrade_of(other), expected);
    }
    fn c<'sess>(t: impl Into<VdBsqLitnumTerm<'sess>>) -> VdBsqNormalizedLitNumBound<'sess> {
        VdBsqNormalizedLitNumBound {
            litnum: t.into(),
            boundary_kind: VdBsqBoundBoundaryKind::Closed,
        }
    }
    fn o<'sess>(t: impl Into<VdBsqLitnumTerm<'sess>>) -> VdBsqNormalizedLitNumBound<'sess> {
        VdBsqNormalizedLitNumBound {
            litnum: t.into(),
            boundary_kind: VdBsqBoundBoundaryKind::Open,
        }
    }
    t(c(1), o(1), false);
    t(o(1), o(1), false);
    t(c(1), c(1), false);
    t(o(1), c(1), true);
    t(c(1), c(2), false);
    t(c(1), o(2), false);
    t(o(1), c(2), false);
    t(o(1), o(2), false);
    t(c(2), c(1), true);
    t(c(2), o(1), true);
    t(o(2), c(1), true);
    t(o(2), o(1), true);
}

impl<'sess> VdBsqNormalizedLitNumBound<'sess> {
    fn unnormalize(
        self,
        factor: VdBsqLitnumTerm<'sess>,
        opr: VdBsqBoundOpr,
        db: &'sess FloaterDb,
    ) -> VdBsqLitNumBound<'sess> {
        VdBsqLitNumBound {
            litnum: self.litnum.mul(factor, db),
            boundary_kind: self.boundary_kind,
            opr,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct VdBsqLitNumBound<'sess> {
    litnum: VdBsqLitnumTerm<'sess>,
    boundary_kind: VdBsqBoundBoundaryKind,
    opr: VdBsqBoundOpr,
}

impl<'sess> VdBsqLitNumBound<'sess> {
    pub fn merge(&mut self, other: VdBsqLitNumBound<'sess>, db: &'sess FloaterDb) {
        assert!(self.opr == other.opr);
        self.litnum = self.litnum.add(other.litnum, db);
        self.boundary_kind = match (self.boundary_kind, other.boundary_kind) {
            (VdBsqBoundBoundaryKind::Open, VdBsqBoundBoundaryKind::Open) => {
                VdBsqBoundBoundaryKind::Open
            }
            _ => VdBsqBoundBoundaryKind::Closed,
        };
    }

    pub fn finalize(self, rhs: VdBsqLitnumTerm<'sess>, db: &'sess FloaterDb) -> bool {
        // range A contains range B means if x is in B, then x is in A
        if self.opr.boundary_kind().contains(self.boundary_kind) {
            if self.litnum == rhs {
                return true;
            }
            match self.opr {
                VdBsqBoundOpr::Lt | VdBsqBoundOpr::Le => self.litnum <= rhs,
                VdBsqBoundOpr::Gt | VdBsqBoundOpr::Ge => self.litnum >= rhs,
            }
        } else {
            match self.opr {
                VdBsqBoundOpr::Lt | VdBsqBoundOpr::Le => self.litnum < rhs,
                VdBsqBoundOpr::Gt | VdBsqBoundOpr::Ge => self.litnum > rhs,
            }
        }
    }
}

impl IsVdBsqHypothesisStashScheme for VdBsqLitNumBoundScheme {
    type Key<'sess> = VdBsqLitNumBoundKey<'sess>;

    type Value<'sess> = VdBsqNormalizedLitNumBound<'sess>;
}

impl IsVdBsqHypothesisUpgradeStashScheme for VdBsqLitNumBoundScheme {
    fn is_new_value_upgrade_of_old<'sess>(
        old: &Self::Value<'sess>,
        new: &Self::Value<'sess>,
    ) -> bool {
        if old == new {
            return false;
        }
        new.is_upgrade_of(*old)
    }

    fn key_value_from_hypothesis<'sess>(
        record: VdBsqHypothesisStackRecord<'sess>,
        entry: &VdBsqHypothesisEntry<'sess>,
        db: &'sess FloaterDb,
    ) -> Option<(Self::Key<'sess>, Self::Value<'sess>)> {
        let VdBsqTerm::Prop(VdBsqPropTerm::NumRelation(term)) = entry.expr().term() else {
            return None;
        };
        let VdBsqComparisonOpr::Bound(opr) = term.opr() else {
            return None;
        };
        require!(let VdBsqNumTerm::Comnum(term) = term.lhs_minus_rhs());
        let (_, (litnum, normalized_monomials)) = split(term, opr, db);
        let lower_bound_litnum = litnum.neg(db);
        let boundary_kind = opr.boundary_kind();
        Some((
            VdBsqLitNumBoundKey {
                normalized_monomials,
            },
            VdBsqNormalizedLitNumBound {
                litnum: lower_bound_litnum,
                boundary_kind,
            },
        ))
    }
}

/// will reduce upper bound to lower bound
fn split<'sess>(
    lhs_minus_rhs: VdBsqComnumTerm<'sess>,
    opr: VdBsqBoundOpr,
    db: &'sess FloaterDb,
) -> (
    VdBsqLitnumTerm<'sess>,
    (VdBsqLitnumTerm<'sess>, VdBsqComnumTerm<'sess>),
) {
    let sign = match opr {
        VdBsqBoundOpr::Lt => VdBsqSign::Minus,
        VdBsqBoundOpr::Gt => VdBsqSign::Plus,
        VdBsqBoundOpr::Le => VdBsqSign::Minus,
        VdBsqBoundOpr::Ge => VdBsqSign::Plus,
    };
    let (factor, (litnum, normalized_monomials)) =
        lhs_minus_rhs.split_sum_fld(|factor| factor.with_sign(sign, db), db);
    (factor, (litnum, normalized_monomials))
}

impl<'sess> VdBsqHypothesisStack<'sess> {
    pub(crate) fn get_active_litnum_bound(
        &self,
        term: VdBsqComnumTerm<'sess>,
        opr: VdBsqBoundOpr,
        db: &'sess FloaterDb,
    ) -> Option<VdBsqLitNumBound<'sess>> {
        self.stashes()
            .litnum_bound()
            .get_active_bound(term, opr, self.active_hypotheses(), db)
    }
}

impl<'sess> VdBsqLitnumBoundStash<'sess> {
    pub(crate) fn get_active_bound(
        &self,
        term: VdBsqComnumTerm<'sess>,
        opr: VdBsqBoundOpr,
        active_hypotheses: &VdBsqActiveHypotheses<'sess>,
        db: &'sess FloaterDb,
    ) -> Option<VdBsqLitNumBound<'sess>> {
        let (factor, (litnum, normalized_monomials)) = split(term, opr, db);
        self.get_active_value_with(
            VdBsqLitNumBoundKey {
                normalized_monomials,
            },
            db,
            active_hypotheses,
            |&value| value.unnormalize(factor, opr, db),
        )
    }
}
