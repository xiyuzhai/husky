use crate::expr::{VdMirExprArenaRef, VdMirExprData, VdMirExprIdx};

pub fn vd_mir_expr_deep_eq(a: VdMirExprIdx, b: VdMirExprIdx, arena: VdMirExprArenaRef) -> bool {
    match (arena[a].data(), arena[b].data()) {
        (VdMirExprData::Literal(a), VdMirExprData::Literal(b)) => a == b,
        (VdMirExprData::ItemPath(a), VdMirExprData::ItemPath(b)) => a == b,
        (VdMirExprData::Variable(a), VdMirExprData::Variable(b)) => a == b,
        (
            VdMirExprData::Application {
                function: a_fn,
                arguments: a_args,
            },
            VdMirExprData::Application {
                function: b_fn,
                arguments: b_args,
            },
        ) => a_fn == b_fn && a_args == b_args,
        (
            VdMirExprData::FoldingSeparatedList {
                leader: a_leader,
                followers: a_followers,
            },
            VdMirExprData::FoldingSeparatedList {
                leader: b_leader,
                followers: b_followers,
            },
        ) => vd_mir_expr_deep_eq(*a_leader, *b_leader, arena) && a_followers == b_followers,
        (
            VdMirExprData::ChainingSeparatedList {
                leader: a_leader,
                followers: a_followers,
                joined_signature: a_sig,
            },
            VdMirExprData::ChainingSeparatedList {
                leader: b_leader,
                followers: b_followers,
                joined_signature: b_sig,
            },
        ) => {
            vd_mir_expr_deep_eq(*a_leader, *b_leader, arena)
                && a_followers == b_followers
                && a_sig == b_sig
        }
        _ => false,
    }
}
