use super::{expr::VdBsqExpr, *};
use cache_trivial_bounds::cache_trivial_boundsm;
use foundations::{bound::VdBsqBoundKind, opr::separator::relation::comparison::VdBsqBoundOpr};
use hypothesis::stashes::litnum_bound::VdBsqLitnumBound;
use term::comnum::VdBsqComnumTerm;

// returns unit because we just cache the results
pub fn litnum_boundm<'db, 'sess>(
    term: VdBsqComnumTerm<'sess>,
    bound_kind: VdBsqBoundKind,
) -> impl ElabM<'db, 'sess, VdBsqLitnumBound<'sess>>
where
    'db: 'sess,
{
    VdBsqManeuverCall::LitnumBound.wrap(
        cache_trivial_boundsm(term).bind(move |elr, ()| litnum_bound_innerm(term, bound_kind)),
    )
}

fn litnum_bound_innerm<'db, 'sess>(
    term: VdBsqComnumTerm<'sess>,
    bound_kind: VdBsqBoundKind,
) -> impl ElabM<'db, 'sess, VdBsqLitnumBound<'sess>>
where
    'db: 'sess,
{
    move |elr: &mut Elr<'db, 'sess>, f: &Heuristic<'_, 'db, 'sess, VdBsqLitnumBound<'sess>>| {
        let Some(bound) = elr.get_active_litnum_bound(term, bound_kind) else {
            return AltNothing;
        };
        f(elr, bound)
    }
}
