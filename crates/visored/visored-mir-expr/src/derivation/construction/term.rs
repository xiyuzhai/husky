use super::*;
use crate::expr::VdMirExprData;
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
            VdMirTermDerivationConstruction::Reflection => todo!(),
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
