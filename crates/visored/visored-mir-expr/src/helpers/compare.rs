use crate::expr::{VdMirExprArenaRef, VdMirExprData, VdMirExprIdx};
use husky_control_flow_utils::require;

#[macro_use]
macro_rules! assert_deep_eq {
    ($a:expr, $b:expr, $hc:expr) => {
        assert!(
            $crate::helpers::compare::vd_mir_expr_deep_eq($a, $b, $hc.expr_arena()),
            "{} = `{}`, {} = `{}`",
            stringify!($a),
            $hc.fmt_expr($a),
            stringify!($b),
            $hc.fmt_expr($b)
        )
    };
}

pub(crate) use assert_deep_eq;
use visored_signature::signature::separator::base::folding::VdBaseFoldingSeparatorSignature;

pub fn vd_mir_expr_deep_eq(a: VdMirExprIdx, b: VdMirExprIdx, arena: VdMirExprArenaRef) -> bool {
    if a == b {
        return true;
    }
    match (arena[a].data(), arena[b].data()) {
        (VdMirExprData::Literal(a), VdMirExprData::Literal(b)) => a == b,
        (VdMirExprData::ItemPath(a), VdMirExprData::ItemPath(b)) => a == b,
        (VdMirExprData::Variable(a), VdMirExprData::Variable(b)) => a == b,
        (
            &VdMirExprData::Application {
                function: a_fn,
                arguments: a_args,
            },
            &VdMirExprData::Application {
                function: b_fn,
                arguments: b_args,
            },
        ) => {
            require!(a_fn == b_fn);
            require!(a_args.len() == b_args.len());
            for (a_arg, b_arg) in a_args.into_iter().zip(b_args) {
                require!(vd_mir_expr_deep_eq(a_arg, b_arg, arena));
            }
            true
        }
        (
            VdMirExprData::FoldingSeparatedList {
                leader: a_leader,
                followers: a_followers,
            },
            VdMirExprData::FoldingSeparatedList {
                leader: b_leader,
                followers: b_followers,
            },
        ) => folding_separated_list_deep_eq(*a_leader, a_followers, *b_leader, b_followers, arena),
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
            require!(vd_mir_expr_deep_eq(*a_leader, *b_leader, arena));
            require!(a_followers.len() == b_followers.len());
            for (&(a_sep, a_follower), &(b_sep, b_follower)) in
                a_followers.into_iter().zip(b_followers)
            {
                require!(a_sep == b_sep);
                require!(vd_mir_expr_deep_eq(a_follower, b_follower, arena));
            }
            true
        }
        _ => false,
    }
}

fn folding_separated_list_deep_eq(
    a_leader: VdMirExprIdx,
    a_followers: &[(VdBaseFoldingSeparatorSignature, VdMirExprIdx)],
    b_leader: VdMirExprIdx,
    b_followers: &[(VdBaseFoldingSeparatorSignature, VdMirExprIdx)],
    arena: VdMirExprArenaRef,
) -> bool {
    let Some(&(last_a_signature, last_a_follower)) = a_followers.last() else {
        return if b_followers.is_empty() {
            vd_mir_expr_deep_eq(a_leader, b_leader, arena)
        } else {
            require!(let &VdMirExprData::FoldingSeparatedList {
                leader: a_leader,
                followers: ref a_followers,
            } = arena[a_leader].data());
            folding_separated_list_deep_eq(a_leader, a_followers, b_leader, b_followers, arena)
        };
    };
    let Some(&(last_b_signature, last_b_follower)) = b_followers.last() else {
        require!(let &VdMirExprData::FoldingSeparatedList {
            leader: b_leader,
            followers: ref b_followers,
        } = arena[b_leader].data());
        return folding_separated_list_deep_eq(a_leader, a_followers, b_leader, b_followers, arena);
    };
    require!(last_a_signature == last_b_signature);
    require!(vd_mir_expr_deep_eq(last_a_follower, last_b_follower, arena));
    folding_separated_list_deep_eq(
        a_leader,
        &a_followers[..a_followers.len() - 1],
        b_leader,
        &b_followers[..b_followers.len() - 1],
        arena,
    )
}
