use super::*;
use visored_opr::separator::VdBaseSeparator;
use visored_sem_expr::expr::separated_list::VdSemSeparatedListFollower;

impl<'a> VdMirExprRegionBuilder<'a> {
    pub(super) fn build_folding_separated_list(
        &mut self,
        leader: VdSemExprIdx,
        followers: &[VdSemSeparatedListFollower],
    ) -> VdMirExprData {
        VdMirExprData::FoldingSeparatedList {
            leader: leader.to_vd_mir(self),
            followers: followers
                .iter()
                .copied()
                .map(|follower| {
                    let VdSemSeparatedListFollowerDispatch::Folding {
                        base_separator,
                        signature,
                    } = follower.dispatch
                    else {
                        unreachable!()
                    };
                    (signature, follower.expr.to_vd_mir(self))
                })
                .collect(),
        }
    }

    pub(super) fn build_chaining_separated_list(
        &mut self,
        leader: VdSemExprIdx,
        followers: &[VdSemSeparatedListFollower],
        joined_chaining_separator_and_signature: Option<(
            VdBaseSeparator,
            VdBaseChainingSeparatorSignature,
        )>,
    ) -> VdMirExprData {
        VdMirExprData::ChainingSeparatedList {
            leader: leader.to_vd_mir(self),
            followers: followers
                .iter()
                .copied()
                .map(|follower| match follower.dispatch {
                    VdSemSeparatedListFollowerDispatch::Chaining {
                        base_separator,
                        signature,
                    } => (signature, follower.expr.to_vd_mir(self)),
                    VdSemSeparatedListFollowerDispatch::InSet { expr_ty } => (
                        VdBaseChainingSeparatorSignature::IN_SET,
                        follower.expr.to_vd_mir(self),
                    ),
                    VdSemSeparatedListFollowerDispatch::Folding {
                        base_separator,
                        signature,
                    } => unreachable!("follower.dispatch = {:?}", follower.dispatch),
                })
                .collect(),
            joined_signature: joined_chaining_separator_and_signature
                .map(|(_, signature)| signature),
        }
    }
}
