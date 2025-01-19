mod neg;
mod sub;
pub mod sum;

use self::{neg::*, sub::*, sum::*};
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
        merge: VdMirTermDerivationIdx,
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

impl VdMirTermDerivationIdx {
    pub fn prop<'db, 'a, Src>(self, hc: &'a VdMirHypothesisConstructor<'db, Src>) -> VdMirExprIdx {
        hc.derivation_arena()[*self].prop()
    }

    pub fn construction<'db, 'a, Src>(
        self,
        hc: &'a VdMirHypothesisConstructor<'db, Src>,
    ) -> &'a VdMirTermDerivationConstruction {
        match hc.derivation_arena()[*self].construction() {
            VdMirDerivationConstruction::Ring(_) => unreachable!(),
            VdMirDerivationConstruction::Term(construction) => construction,
        }
    }
}

impl VdMirTermDerivationConstruction {
    pub fn check<'db, Src>(
        &self,
        prop: VdMirExprIdx,
        hc: &mut VdMirHypothesisConstructor<'db, Src>,
    ) {
        let expr_arena = hc.expr_arena();
        let VdMirExprData::ChainingSeparatedList {
            leader: lhs,
            ref followers,
            joined_signature: None,
        } = *expr_arena[prop].data()
        else {
            unreachable!()
        };
        let (signature, rhs) = followers[0];
        match *self {
            VdMirTermDerivationConstruction::Reflection => {
                check_reflection(lhs, signature, rhs, hc)
            }
            VdMirTermDerivationConstruction::LiteralAdd => check_add_literal(lhs, rhs, hc),
            VdMirTermDerivationConstruction::NumComparison {
                lhs_minus_rhs: lhs_minus_rhs_equivalence,
            } => check_num_comparison(lhs, signature, rhs, hc),
            VdMirTermDerivationConstruction::SubEqsAddNeg { add_neg } => {
                check_sub_eqs_add_neg(lhs, signature, rhs, add_neg, hc)
            }
            VdMirTermDerivationConstruction::AdditionInterchange => {
                check_add_interchange(lhs, signature, rhs, hc)
            }
            VdMirTermDerivationConstruction::AdditionAssociativity => todo!(),
            VdMirTermDerivationConstruction::AdditionIdentity => todo!(),
            VdMirTermDerivationConstruction::AdditionInverse => todo!(),
            VdMirTermDerivationConstruction::AdditionDistributivity => todo!(),
            VdMirTermDerivationConstruction::NegLiteral => {
                check_neg_literal(lhs, signature, rhs, hc)
            }
            VdMirTermDerivationConstruction::AddEq {
                lopd, ropd, merge, ..
            } => check_add_eq(lhs, signature, rhs, lopd, ropd, merge, hc),
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
