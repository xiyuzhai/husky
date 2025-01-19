use super::*;
use crate::{
    coercion::VdBsqCoercionOutcome,
    elabm::{foldm::mapm_collect, ElabM},
    expr::{VdBsqExpr, VdBsqExprData},
    hypothesis::construction::VdBsqHypothesisConstruction,
    Mhr,
};
use alt_option::*;
use elabm::Pure;
use expr::{VdBsqExprChainingFollowers, VdBsqExprFoldingFollowers};
use smallvec::SmallVec;
use visored_baseq_elaborator_macros::unify_elabm;
use visored_entity_path::{
    path::{
        set::{VdPreludeSetPath, VdSetPath},
        VdItemPath,
    },
    theorem::VdTheoremPath,
};
use visored_mir_expr::expr::application::VdMirFunc;
use visored_mir_opr::separator::VdMirBaseSeparator;
use visored_term::term::VdTerm;

pub(crate) fn litnum_rewritem<'db, 'sess>(
    expr: VdBsqExpr<'sess>,
) -> impl ElabM<'db, 'sess, VdBsqExpr<'sess>>
where
    'db: 'sess,
{
    VdBsqManeuverCall::LitnumRewrite.wrap(litnum_rewrite_inner(expr))
}

fn litnum_rewrite_inner<'db, 'sess>(
    expr: VdBsqExpr<'sess>,
) -> impl ElabM<'db, 'sess, VdBsqExpr<'sess>>
where
    'db: 'sess,
{
    move |elaborator: &mut Elr<'db, 'sess>,
          heuristic: &Heuristic<'_, 'db, 'sess, VdBsqExpr<'sess>>| {
        let db = elaborator.floater_db();
        match elaborator.hc.stack().get_active_litnum_equality(expr, db) {
            Some(litnum) => {
                let litnum = elaborator.mk_lit(litnum, expr.ty());
                Pure(litnum).eval(elaborator, heuristic)
            }
            None => rewrite_subexprs(expr, litnum_rewrite_inner).eval(elaborator, heuristic),
        }
    }
}

fn rewrite_subexprs<'a, 'db, 'sess, MExpr>(
    expr: VdBsqExpr<'sess>,
    f: impl Fn(VdBsqExpr<'sess>) -> MExpr + Copy + 'a,
) -> impl ElabM<'db, 'sess, VdBsqExpr<'sess>> + 'a
where
    'db: 'sess + 'a,
    'sess: 'a,
    MExpr: ElabM<'db, 'sess, VdBsqExpr<'sess>> + 'a,
{
    #[unify_elabm]
    match *expr.data() {
        VdBsqExprData::Literal(_) | VdBsqExprData::Variable(_, _) | VdBsqExprData::ItemPath(_) => {
            Pure(expr)
        }
        VdBsqExprData::Application {
            function,
            ref arguments,
        } =>
        {
            #[unify_elabm]
            match function {
                VdMirFunc::NormalBasePrefixOpr(_)
                | VdMirFunc::NormalBaseSeparator(_)
                | VdMirFunc::NormalBaseBinaryOpr(_)
                | VdMirFunc::Power(_)
                | VdMirFunc::NormalBaseSqrt(_) => mapm_collect(arguments, |&argument| f(argument))
                    .map(|elr, arguments| {
                        elr.mk_expr(
                            VdBsqExprData::Application {
                                function,
                                arguments,
                            },
                            expr.ty(),
                        )
                    }),
            }
        }
        VdBsqExprData::FoldingSeparatedList {
            leader,
            ref followers,
        } => f(leader).bind(|elr, leader| {
            mapm_collect(followers, |&(func, follower)| {
                f(follower).map(move |elr, follower| (func, follower))
            })
            .map(move |elr, followers: VdBsqExprFoldingFollowers<'sess>| {
                elr.mk_expr(
                    VdBsqExprData::FoldingSeparatedList { leader, followers },
                    expr.ty(),
                )
            })
        }),
        VdBsqExprData::ChainingSeparatedList {
            leader,
            ref followers,
            joined_signature,
        } => f(leader).bind(|elr, leader| {
            mapm_collect(followers, |&(func, follower)| {
                f(follower).map(move |elr, follower| (func, follower))
            })
            .map(move |elr, followers: VdBsqExprChainingFollowers<'sess>| {
                elr.mk_expr(
                    VdBsqExprData::ChainingSeparatedList {
                        leader,
                        followers,
                        joined_signature,
                    },
                    expr.ty(),
                )
            })
        }),
    }
}
