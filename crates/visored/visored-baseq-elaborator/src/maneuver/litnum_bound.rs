use super::{expr::VdBsqExpr, *};
use cache_trivial_bounds::cache_trivial_boundsm;
use hypothesis::stashes::litnum_bound::VdBsqLitnumBound;
use term::comnum::VdBsqComnumTerm;

// returns unit because we just cache the results
pub fn litnum_boundm<'db, 'sess>(
    term: VdBsqComnumTerm<'sess>,
) -> impl ElabM<'db, 'sess, VdBsqLitnumBound>
where
    'db: 'sess,
{
    VdBsqManeuverCall::LitnumBound
        .wrap(cache_trivial_boundsm(term).bind(move |elr, ()| litnum_bound_innerm(term)))
}

fn litnum_bound_innerm<'db, 'sess>(
    term: VdBsqComnumTerm<'sess>,
) -> impl ElabM<'db, 'sess, VdBsqLitnumBound>
where
    'db: 'sess,
{
    todo!()
}
