use super::{expr::VdBsqExpr, *};

// returns unit because we just cache the results
pub fn cache_trivial_boundsm<'db, 'sess>(expr: VdBsqExpr<'sess>) -> impl ElabM<'db, 'sess, ()>
where
    'db: 'sess,
{
    todo!()
}
