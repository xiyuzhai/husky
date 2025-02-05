//! this stores the best litnum bounds for terms
mod normalized;

use self::normalized::*;
use super::*;
use crate::{
    expr::VdBsqExpr,
    foundations::{
        bound::VdBsqBoundKind,
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
    Elr,
};
use floated_sequential::db::FloaterDb;
use husky_control_flow_utils::require;

pub type VdBsqLitnumBoundHypothesisStash<'sess> =
    VdBsqHypothesisUpgradeStash<'sess, VdBsqLitnumBoundScheme>;

pub struct VdBsqLitnumBoundScheme;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct VdBsqLitnumBound<'sess> {
    src: VdBsqLitnumBoundSrc<'sess>,
    litnum_factor: VdBsqLitnumTerm<'sess>,
    litnum_summand: VdBsqLitnumTerm<'sess>,
    bound_litnum: VdBsqLitnumTerm<'sess>,
    boundary_kind: VdBsqBoundBoundaryKind,
}

/// the hypothesis is term equivalent to `litnum_factor * (litnum_summand + normalized_monomials) <relationship> 0`
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct VdBsqLitnumBoundSrc<'sess> {
    hypothesis: VdBsqHypothesisIdx<'sess>,
    litnum_factor: VdBsqLitnumTerm<'sess>,
    litnum_summand: VdBsqLitnumTerm<'sess>,
}

impl<'sess> VdBsqLitnumBound<'sess> {
    pub fn src(&self) -> VdBsqLitnumBoundSrc<'sess> {
        self.src
    }

    pub fn litnum_factor(&self) -> VdBsqLitnumTerm<'sess> {
        self.litnum_factor
    }

    pub fn litnum_summand(&self) -> VdBsqLitnumTerm<'sess> {
        self.litnum_summand
    }

    pub fn bound_litnum(&self) -> VdBsqLitnumTerm<'sess> {
        self.bound_litnum
    }

    pub fn boundary_kind(&self) -> VdBsqBoundBoundaryKind {
        self.boundary_kind
    }
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
    pub fn try_infer(
        self,
        opr: VdBsqBoundOpr,
        rhs: VdBsqLitnumTerm<'sess>,
        db: &'sess FloaterDb,
    ) -> bool {
        // range A contains range B means if x is in B, then x is in A
        if opr.boundary_kind().contains(self.boundary_kind) {
            if self.bound_litnum == rhs {
                return true;
            }
            match opr {
                VdBsqBoundOpr::Lt | VdBsqBoundOpr::Le => self.bound_litnum <= rhs,
                VdBsqBoundOpr::Gt | VdBsqBoundOpr::Ge => self.bound_litnum >= rhs,
            }
        } else {
            match opr {
                VdBsqBoundOpr::Lt | VdBsqBoundOpr::Le => self.bound_litnum < rhs,
                VdBsqBoundOpr::Gt | VdBsqBoundOpr::Ge => self.bound_litnum > rhs,
            }
        }
    }
}

impl IsVdBsqHypothesisStashScheme for VdBsqLitnumBoundScheme {
    type Key<'sess> = VdBsqNormalizedLitnumBoundKey<'sess>;

    type Value<'sess> = VdBsqNormalizedLitnumBound<'sess>;
}

impl IsVdBsqHypothesisUpgradeStashScheme for VdBsqLitnumBoundScheme {
    fn is_new_value_upgrade_of_old<'sess>(
        &old: &Self::Value<'sess>,
        &new: &Self::Value<'sess>,
    ) -> bool {
        new.is_upgrade_of(old)
    }

    fn key_value_from_hypothesis<'sess>(
        record: VdBsqHypothesisStackRecord<'sess>,
        entry: &VdBsqHypothesisEntry<'sess>,
        db: &'sess FloaterDb,
    ) -> Option<(Self::Key<'sess>, Self::Value<'sess>)> {
        let VdBsqTerm::Prop(VdBsqPropTerm::NumRelation(term)) = entry.prop().term() else {
            return None;
        };
        let VdBsqComparisonOpr::Bound(opr) = term.opr() else {
            return None;
        };
        require!(let VdBsqNumTerm::Comnum(term) = term.lhs_minus_rhs());
        let (litnum_factor, (litnum_summand, normalized_monomials)) =
            split(term, opr.bound_kind(), db);
        let lower_bound_litnum = litnum_summand.neg(db);
        let boundary_kind = opr.boundary_kind();
        let src = VdBsqLitnumBoundSrc {
            hypothesis: record.hypothesis_idx(),
            litnum_factor,
            litnum_summand,
        };
        Some((
            VdBsqNormalizedLitnumBoundKey::new(normalized_monomials),
            VdBsqNormalizedLitnumBound::new(src, lower_bound_litnum, boundary_kind),
        ))
    }
}

/// will reduce upper bound to lower bound
fn split<'sess>(
    lhs_minus_rhs: VdBsqComnumTerm<'sess>,
    bound_kind: VdBsqBoundKind,
    db: &'sess FloaterDb,
) -> (
    VdBsqLitnumTerm<'sess>,
    (VdBsqLitnumTerm<'sess>, VdBsqComnumTerm<'sess>),
) {
    let sign = match bound_kind {
        VdBsqBoundKind::Upper => VdBsqSign::Minus,
        VdBsqBoundKind::Lower => VdBsqSign::Plus,
    };
    let (factor, (litnum, normalized_monomials)) =
        lhs_minus_rhs.split_sum_fld(|factor| factor.with_sign(sign, db), db);
    (factor, (litnum, normalized_monomials))
}

impl<'db, 'sess> Elr<'db, 'sess> {
    pub(crate) fn get_active_litnum_bound(
        &self,
        term: VdBsqComnumTerm<'sess>,
        bound_kind: VdBsqBoundKind,
    ) -> Option<VdBsqLitnumBound<'sess>> {
        let db = self.floater_db();
        self.hc
            .stack()
            .get_active_litnum_bound(term, bound_kind, db)
    }
}

impl<'sess> VdBsqHypothesisStack<'sess> {
    fn get_active_litnum_bound(
        &self,
        term: VdBsqComnumTerm<'sess>,
        bound_kind: VdBsqBoundKind,
        db: &'sess FloaterDb,
    ) -> Option<VdBsqLitnumBound<'sess>> {
        self.stashes().litnum_bound().get_active_bound(
            term,
            bound_kind,
            self.active_hypotheses(),
            db,
        )
    }
}

impl<'sess> VdBsqLitnumBoundHypothesisStash<'sess> {
    fn get_active_bound(
        &self,
        term: VdBsqComnumTerm<'sess>,
        bound_kind: VdBsqBoundKind,
        active_hypotheses: &VdBsqActiveHypotheses<'sess>,
        db: &'sess FloaterDb,
    ) -> Option<VdBsqLitnumBound<'sess>> {
        let (litnum_factor, (litnum_summand, normalized_monomials)) = split(term, bound_kind, db);
        self.get_active_value_with(
            VdBsqNormalizedLitnumBoundKey::new(normalized_monomials),
            db,
            active_hypotheses,
            |&normalized_bound| normalized_bound.unnormalize(litnum_factor, litnum_summand, db),
        )
    }
}
