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
        VdBsqHypothesisIdx,
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

pub type VdBsqLitnumBoundStash<'sess> = VdBsqHypothesisUpgradeStash<'sess, VdBsqLitnumBoundScheme>;

pub struct VdBsqLitnumBoundScheme;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VdBsqLitnumBoundKey<'sess> {
    normalized_monomials: VdBsqComnumTerm<'sess>,
}

/// always a lower bound
///
/// `litnum` is the right hand side constant
///
/// `boundary_kind` indicates whether it's closed or open
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct VdBsqNormalizedLitnumBound<'sess> {
    lower_bound_litnum: VdBsqLitnumTerm<'sess>,
    boundary_kind: VdBsqBoundBoundaryKind,
}

impl<'sess> VdBsqNormalizedLitnumBound<'sess> {
    pub fn is_upgrade_of(self, other: Self) -> bool {
        self > other
    }
}

#[test]
fn vd_bsq_normalized_litnum_bound_is_upgrade_works() {
    fn t<'sess>(
        slf: VdBsqNormalizedLitnumBound<'sess>,
        other: VdBsqNormalizedLitnumBound<'sess>,
        expected: bool,
    ) {
        assert_eq!(slf.is_upgrade_of(other), expected);
    }
    fn c<'sess>(t: impl Into<VdBsqLitnumTerm<'sess>>) -> VdBsqNormalizedLitnumBound<'sess> {
        VdBsqNormalizedLitnumBound {
            lower_bound_litnum: t.into(),
            boundary_kind: VdBsqBoundBoundaryKind::Closed,
        }
    }
    fn o<'sess>(t: impl Into<VdBsqLitnumTerm<'sess>>) -> VdBsqNormalizedLitnumBound<'sess> {
        VdBsqNormalizedLitnumBound {
            lower_bound_litnum: t.into(),
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

impl<'sess> VdBsqNormalizedLitnumBound<'sess> {
    fn unnormalize(
        self,
        litnum_factor: VdBsqLitnumTerm<'sess>,
        litnum_summand: VdBsqLitnumTerm<'sess>,
        opr: VdBsqBoundOpr,
        db: &'sess FloaterDb,
    ) -> VdBsqLitnumBound<'sess> {
        VdBsqLitnumBound {
            bound_litnum: self
                .lower_bound_litnum
                .add(litnum_summand, db)
                .mul(litnum_factor, db),
            boundary_kind: self.boundary_kind,
            opr,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct VdBsqLitnumBound<'sess> {
    bound_litnum: VdBsqLitnumTerm<'sess>,
    boundary_kind: VdBsqBoundBoundaryKind,
    opr: VdBsqBoundOpr,
}

/// the hypothesis is term equivalent to `litnum_factor * (litnum_summand + normalized_monomials) <relationship> 0`
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct VdBsqLitnumBoundSrc<'sess> {
    hypothesis: VdBsqHypothesisIdx<'sess>,
    litnum_factor: VdBsqLitnumTerm<'sess>,
    litnum_summand: VdBsqLitnumTerm<'sess>,
}

impl<'sess> VdBsqLitnumBoundSrc<'sess> {
    pub fn hypothesis(&self) -> VdBsqHypothesisIdx<'sess> {
        self.hypothesis
    }

    pub fn litnum_factor(&self) -> VdBsqLitnumTerm<'sess> {
        self.litnum_factor
    }

    pub fn litnum_summand(&self) -> VdBsqLitnumTerm<'sess> {
        self.litnum_summand
    }
}

impl<'sess> VdBsqLitnumBound<'sess> {
    pub fn merge(&mut self, other: VdBsqLitnumBound<'sess>, db: &'sess FloaterDb) {
        assert!(self.opr == other.opr);
        self.bound_litnum = self.bound_litnum.add(other.bound_litnum, db);
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
            if self.bound_litnum == rhs {
                return true;
            }
            match self.opr {
                VdBsqBoundOpr::Lt | VdBsqBoundOpr::Le => self.bound_litnum <= rhs,
                VdBsqBoundOpr::Gt | VdBsqBoundOpr::Ge => self.bound_litnum >= rhs,
            }
        } else {
            match self.opr {
                VdBsqBoundOpr::Lt | VdBsqBoundOpr::Le => self.bound_litnum < rhs,
                VdBsqBoundOpr::Gt | VdBsqBoundOpr::Ge => self.bound_litnum > rhs,
            }
        }
    }
}

impl IsVdBsqHypothesisStashScheme for VdBsqLitnumBoundScheme {
    type Key<'sess> = VdBsqLitnumBoundKey<'sess>;

    type Value<'sess> = (
        VdBsqLitnumBoundSrc<'sess>,
        VdBsqNormalizedLitnumBound<'sess>,
    );
}

impl IsVdBsqHypothesisUpgradeStashScheme for VdBsqLitnumBoundScheme {
    fn is_new_value_upgrade_of_old<'sess>(
        &(_, old): &Self::Value<'sess>,
        &(_, new): &Self::Value<'sess>,
    ) -> bool {
        if old == new {
            return false;
        }
        new.is_upgrade_of(old)
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
        let (litnum_factor, (litnum_summand, normalized_monomials)) = split(term, opr, db);
        let lower_bound_litnum = litnum_summand.neg(db);
        let boundary_kind = opr.boundary_kind();
        let src = VdBsqLitnumBoundSrc {
            hypothesis: record.hypothesis_idx(),
            litnum_factor,
            litnum_summand,
        };
        Some((
            VdBsqLitnumBoundKey {
                normalized_monomials,
            },
            (
                src,
                VdBsqNormalizedLitnumBound {
                    lower_bound_litnum,
                    boundary_kind,
                },
            ),
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
    ) -> Option<(VdBsqLitnumBoundSrc<'sess>, VdBsqLitnumBound<'sess>)> {
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
    ) -> Option<(VdBsqLitnumBoundSrc<'sess>, VdBsqLitnumBound<'sess>)> {
        let (litnum_factor, (litnum_summand, normalized_monomials)) = split(term, opr, db);
        self.get_active_value_with(
            VdBsqLitnumBoundKey {
                normalized_monomials,
            },
            db,
            active_hypotheses,
            |&(src, value)| {
                (
                    src,
                    value.unnormalize(litnum_factor, litnum_summand, opr, db),
                )
            },
        )
    }
}
