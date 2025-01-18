use super::*;
use crate::{expr::VdMirExprData, helpers::compare::vd_mir_expr_deep_eq};
use visored_mir_opr::separator::chaining::{
    VdMirBaseChainingSeparator, VdMirBaseComparisonSeparator, VdMirBaseRelationSeparator,
};
use visored_signature::signature::separator::base::chaining::VdBaseChainingSeparatorSignature;

#[derive(Debug, PartialEq, Eq)]
pub enum VdMirTermDerivationConstruction {
    Reflection,
    AdditionInterchange,
    AdditionAssociativity,
    AdditionIdentity,
    AdditionInverse,
    AdditionDistributivity,
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
            VdMirTermDerivationConstruction::AdditionInterchange => {
                check_add_interchange(leader, signature, follower, hc)
            }
            VdMirTermDerivationConstruction::AdditionAssociativity => todo!(),
            VdMirTermDerivationConstruction::AdditionIdentity => todo!(),
            VdMirTermDerivationConstruction::AdditionInverse => todo!(),
            VdMirTermDerivationConstruction::AdditionDistributivity => todo!(),
        }
    }
}

fn check_reflection<'db, Src>(
    leader: VdMirExprIdx,
    signature: VdBaseChainingSeparatorSignature,
    follower: VdMirExprIdx,
    hypothesis_constructor: &VdMirHypothesisConstructor<'db, Src>,
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
    assert!(vd_mir_expr_deep_eq(
        leader,
        follower,
        hypothesis_constructor.expr_arena()
    ))
}

/// obtain `a + (b + c) = term` from `a + b + c = term`
fn check_add_interchange<'db, Src>(
    leader: VdMirExprIdx,
    signature: VdBaseChainingSeparatorSignature,
    follower: VdMirExprIdx,
    hypothesis_constructor: &VdMirHypothesisConstructor<'db, Src>,
) {
    todo!()
    // let expr_arena = hypothesis_constructor.expr_arena();
}

/// obtain `a + b = term` from `a_term + b_term = term` where `a_term` and `b_term` are term reductions of `a` and `b`
fn check_add_eq<'db, Src>(
    leader: VdMirExprIdx,
    signature: VdBaseChainingSeparatorSignature,
    follower: VdMirExprIdx,
    hypothesis_constructor: &VdMirHypothesisConstructor<'db, Src>,
) {
    todo!()
}
