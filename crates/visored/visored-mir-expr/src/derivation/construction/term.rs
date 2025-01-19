mod neg;
pub mod sum;

use self::{neg::*, sum::*};
use super::*;
use crate::{
    derivation::VdMirDerivationIdx, expr::VdMirExprData, helpers::compare::vd_mir_expr_deep_eq,
};
use visored_mir_opr::separator::chaining::{
    VdMirBaseChainingSeparator, VdMirBaseComparisonSeparator, VdMirBaseRelationSeparator,
};
use visored_signature::signature::separator::base::chaining::VdBaseChainingSeparatorSignature;

#[derive(Debug, PartialEq, Eq)]
pub enum VdMirTermDerivationConstruction {
    Reflection,
    NumComparison {
        lhs_minus_rhs: VdMirTermDerivationIdx,
    },
    SubEqsAddNeg {
        add_neg: VdMirTermDerivationIdx,
    },
    LiteralAdd,
    /// derive `a + b => term` from `a => term_a`, `b => term_b` and `term_a + term_b => term`
    AddEq {
        lopd: VdMirTermDerivationIdx,
        ropd: VdMirTermDerivationIdx,
        sum: VdMirTermDerivationIdx,
    },
    AdditionInterchange,
    AdditionAssociativity,
    AdditionIdentity,
    AdditionInverse,
    AdditionDistributivity,
    NegLiteral,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct VdMirTermDerivationIdx(VdMirDerivationIdx);

impl std::ops::Deref for VdMirTermDerivationIdx {
    type Target = VdMirDerivationIdx;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'db, Src> VdMirHypothesisConstructor<'db, Src> {
    pub fn alloc_term_derivation(
        &mut self,
        prop: VdMirExprIdx,
        construction: VdMirTermDerivationConstruction,
    ) -> VdMirTermDerivationIdx {
        let idx = self.alloc_derivation(prop, construction.into());
        VdMirTermDerivationIdx(idx)
    }
}

impl VdMirTermDerivationConstruction {
    pub fn check<'db, Src>(&self, prop: VdMirExprIdx, hc: &VdMirHypothesisConstructor<'db, Src>) {
        let expr_arena = hc.expr_arena();
        let VdMirExprData::ChainingSeparatedList {
            leader,
            ref followers,
            joined_signature: None,
        } = *expr_arena[prop].data()
        else {
            unreachable!()
        };
        let (signature, follower) = followers[0];
        match self {
            VdMirTermDerivationConstruction::Reflection => {
                check_reflection(leader, signature, follower, hc)
            }
            VdMirTermDerivationConstruction::LiteralAdd => check_literal_sum(leader, follower, hc),
            VdMirTermDerivationConstruction::NumComparison {
                lhs_minus_rhs: lhs_minus_rhs_equivalence,
            } => check_num_comparison(leader, signature, follower, hc),
            VdMirTermDerivationConstruction::SubEqsAddNeg { add_neg } => {
                check_sub_eqs_add_neg(leader, signature, follower, hc)
            }
            VdMirTermDerivationConstruction::AdditionInterchange => {
                check_add_interchange(leader, signature, follower, hc)
            }
            VdMirTermDerivationConstruction::AdditionAssociativity => todo!(),
            VdMirTermDerivationConstruction::AdditionIdentity => todo!(),
            VdMirTermDerivationConstruction::AdditionInverse => todo!(),
            VdMirTermDerivationConstruction::AdditionDistributivity => todo!(),
            VdMirTermDerivationConstruction::NegLiteral => {
                check_neg_literal(leader, signature, follower, hc)
            }
            VdMirTermDerivationConstruction::AddEq { .. } => todo!(),
        }
    }
}

fn check_reflection<'db, Src>(
    leader: VdMirExprIdx,
    signature: VdBaseChainingSeparatorSignature,
    follower: VdMirExprIdx,
    hc: &VdMirHypothesisConstructor<'db, Src>,
) {
    match signature.separator() {
        VdMirBaseChainingSeparator::Iff => (),
        VdMirBaseChainingSeparator::Relation(separator) => match separator {
            VdMirBaseRelationSeparator::Comparison(separator) => match separator {
                VdMirBaseComparisonSeparator::Eq => (),
                VdMirBaseComparisonSeparator::Ne => panic!(),
                VdMirBaseComparisonSeparator::Lt => panic!(),
                VdMirBaseComparisonSeparator::Gt => panic!(),
                VdMirBaseComparisonSeparator::Le => todo!("should we allow this?"),
                VdMirBaseComparisonSeparator::Ge => todo!("should we allow this?"),
            },
            VdMirBaseRelationSeparator::Containment(_) => panic!(),
        },
    }
    assert!(vd_mir_expr_deep_eq(leader, follower, hc.expr_arena()))
}

fn check_num_comparison<'db, Src>(
    leader: VdMirExprIdx,
    signature: VdBaseChainingSeparatorSignature,
    follower: VdMirExprIdx,
    hc: &VdMirHypothesisConstructor<'db, Src>,
) {
    todo!()
}

/// obtain `a - b = term` from `a + (-b) = term`
fn check_sub_eqs_add_neg<'db, Src>(
    leader: VdMirExprIdx,
    signature: VdBaseChainingSeparatorSignature,
    follower: VdMirExprIdx,
    hc: &VdMirHypothesisConstructor<'db, Src>,
) {
    todo!()
}

/// obtain `a + (b + c) = term` from `a + b + c = term`
fn check_add_interchange<'db, Src>(
    leader: VdMirExprIdx,
    signature: VdBaseChainingSeparatorSignature,
    follower: VdMirExprIdx,
    hc: &VdMirHypothesisConstructor<'db, Src>,
) {
    todo!()
    // let expr_arena = hc.expr_arena();
}

/// obtain `a + b = term` from `a_term + b_term = term` where `a_term` and `b_term` are term reductions of `a` and `b`
fn check_add_eq<'db, Src>(
    leader: VdMirExprIdx,
    signature: VdBaseChainingSeparatorSignature,
    follower: VdMirExprIdx,
    hc: &VdMirHypothesisConstructor<'db, Src>,
) {
    todo!()
}
