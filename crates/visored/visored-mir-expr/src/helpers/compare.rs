use crate::expr::{VdMirExprArenaRef, VdMirExprData, VdMirExprIdx};
use husky_control_flow_utils::require;

#[macro_use]
macro_rules! eq {
    ($a:expr, $b:expr, $hc:expr) => {
        assert!(
            $crate::helpers::compare::vd_mir_expr_deep_eq($a, $b, $hc.expr_arena()),
            "{} = `{}`, {} = `{}`",
            stringify!($a),
            $hc.show_expr_lisp($a),
            stringify!($b),
            $hc.show_expr_lisp($b)
        );
    };
}

pub(crate) use eq;

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
