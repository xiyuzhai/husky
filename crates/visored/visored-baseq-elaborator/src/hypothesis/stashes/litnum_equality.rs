use super::*;
use crate::{
    expr::VdBsqExpr,
    foundations::opr::separator::relation::comparison::VdBsqComparisonOpr,
    hypothesis::{
        stack::VdBsqHypothesisStack,
        stash::{
            unique::{IsVdBsqHypothesisUniqueStashScheme, VdBsqHypothesisUniqueStash},
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

pub type LitnumEqualityStash<'sess> = VdBsqHypothesisUniqueStash<'sess, VdBsqLitnumEqualityScheme>;

pub struct VdBsqLitnumEqualityScheme;

impl IsVdBsqHypothesisStashScheme for VdBsqLitnumEqualityScheme {
    type Key<'sess> = VdBsqLitnumEqualityKey<'sess>;

    type Value<'sess> = VdBsqLitnumEqualityValue<'sess>;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VdBsqLitnumEqualityKey<'sess> {
    normalized_monomials: VdBsqComnumTerm<'sess>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VdBsqLitnumEqualityValue<'sess> {
    litnum: VdBsqLitnumTerm<'sess>,
}

impl<'sess> VdBsqLitnumEqualityValue<'sess> {
    pub fn litnum(&self) -> VdBsqLitnumTerm<'sess> {
        self.litnum
    }
}

impl IsVdBsqHypothesisUniqueStashScheme for VdBsqLitnumEqualityScheme {
    fn key_value_from_hypothesis<'sess>(
        record: VdBsqHypothesisStackRecord<'sess>,
        entry: &VdBsqHypothesisEntry<'sess>,
        db: &'sess FloaterDb,
    ) -> Option<(Self::Key<'sess>, Self::Value<'sess>)> {
        let VdBsqTerm::Prop(VdBsqPropTerm::NumRelation(term)) = entry.prop().term() else {
            return None;
        };
        require!(term.opr() == VdBsqComparisonOpr::Eq);
        require!(let VdBsqNumTerm::Comnum(VdBsqComnumTerm::Sum(lhs_minus_rhs)) = term.lhs_minus_rhs());
        let (_, (normalized_constant_litnum, normalized_monomials)) =
            lhs_minus_rhs.split_fld(|f| f, db);
        let neg_normalized_constant_litnum = normalized_constant_litnum.neg(db);
        let key = VdBsqLitnumEqualityKey {
            normalized_monomials,
        };
        let value = VdBsqLitnumEqualityValue {
            litnum: neg_normalized_constant_litnum,
        };
        Some((key, value))
    }
}

impl<'sess> LitnumEqualityStash<'sess> {
    pub fn reduce(
        &self,
        term: VdBsqComnumTerm<'sess>,
        active_hypotheses: &VdBsqActiveHypotheses<'sess>,
        db: &'sess FloaterDb,
    ) -> Option<VdBsqLitnumTerm<'sess>> {
        /// decompose `t = a(b + x)`
        let (a, (b, x)): (
            VdBsqLitnumTerm<'sess>,
            (VdBsqLitnumTerm<'sess>, VdBsqComnumTerm<'sess>),
        ) = match term {
            VdBsqComnumTerm::Atom(atom) => {
                (VdBsqLitnumTerm::ONE, (VdBsqLitnumTerm::ZERO, atom.into()))
            }
            VdBsqComnumTerm::Sum(sum) => sum.split_fld(|f| f, db),
            VdBsqComnumTerm::Product(product) => (
                product.litnum_factor(),
                (VdBsqLitnumTerm::ZERO, product.stem().into()),
            ),
        };
        let key = VdBsqLitnumEqualityKey {
            normalized_monomials: x,
        };
        let value = self.get_valid_value(&key, active_hypotheses)?.litnum;
        Some(a.mul(value.add(b, db), db))
    }
}

impl<'sess> VdBsqHypothesisStack<'sess> {
    pub(crate) fn get_active_litnum_equality(
        &self,
        expr: VdBsqExpr<'sess>,
        db: &'sess FloaterDb,
    ) -> Option<VdBsqLitnumTerm<'sess>> {
        let VdBsqNumTerm::Comnum(term) = expr.term().num()? else {
            return None;
        };
        self.stashes()
            .litnum_equality()
            .reduce(term, self.active_hypotheses(), db)
    }
}
