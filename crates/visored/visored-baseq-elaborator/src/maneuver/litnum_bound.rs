use super::{expr::VdBsqExpr, *};
use cache_trivial_bounds::cache_trivial_boundsm;
use hypothesis::stashes::litnum_bound::VdBsqLitnumBound;
use term::comnum::VdBsqComnumTerm;

// returns unit because we just cache the results
pub fn litnum_boundsm<'db, 'sess>(
    term: VdBsqComnumTerm<'sess>,
) -> impl ElabM<'db, 'sess, VdBsqLitnumBound>
where
    'db: 'sess,
{
    VdBsqManeuverCall::LitnumBound
        .wrap(cache_trivial_boundsm(term).bind(move |engine, _| litnum_bound_inner(term)))
}

fn litnum_bound_inner<'db, 'sess>(
    term: VdBsqComnumTerm<'sess>,
) -> impl ElabM<'db, 'sess, VdBsqLitnumBound>
where
    'db: 'sess,
{
    todo!()
}
