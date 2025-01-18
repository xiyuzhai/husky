use visored_signature::signature::separator::base::chaining::VdBaseChainingSeparatorSignature;

use crate::{
    expr::{VdMirExprData, VdMirExprIdx},
    hypothesis::constructor::VdMirHypothesisConstructor,
};

#[derive(Debug, PartialEq, Eq)]
pub enum VdMirRingDerivationConstruction {
    AdditionInterchange,
    AdditionAssociativity,
    AdditionIdentity,
    AdditionInverse,
    AdditionDistributivity,
}

impl VdMirRingDerivationConstruction {
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
            VdMirRingDerivationConstruction::AdditionInterchange => {
                check_add_interchange(leader, signature, follower, hc)
            }
            VdMirRingDerivationConstruction::AdditionAssociativity => todo!(),
            VdMirRingDerivationConstruction::AdditionIdentity => todo!(),
            VdMirRingDerivationConstruction::AdditionInverse => todo!(),
            VdMirRingDerivationConstruction::AdditionDistributivity => todo!(),
        }
    }
}

fn check_add_interchange<'db, Src>(
    leader: VdMirExprIdx,
    signature: VdBaseChainingSeparatorSignature,
    follower: VdMirExprIdx,
    hypothesis_constructor: &VdMirHypothesisConstructor<'db, Src>,
) {
    todo!()
    // let expr_arena = hypothesis_constructor.expr_arena();
}
