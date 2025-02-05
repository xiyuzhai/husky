use super::{expr::VdBsqExpr, *};
use cache_trivial_bounds::cache_trivial_boundsm;

// returns unit because we just cache the results
pub fn litnum_boundsm<'db, 'sess>(expr: VdBsqExpr<'sess>) -> impl ElabM<'db, 'sess, ()>
where
    'db: 'sess,
{
    VdBsqManeuverCall::LitnumBound
        .wrap(cache_trivial_boundsm(expr).bind(move |engine, _| litnum_bound_inner(expr)))
}

fn litnum_bound_inner<'db, 'sess>(expr: VdBsqExpr<'sess>) -> impl ElabM<'db, 'sess, ()>
where
    'db: 'sess,
{
    todo!()
}
