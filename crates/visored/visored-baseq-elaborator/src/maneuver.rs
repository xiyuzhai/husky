pub mod cache_trivial_bounds;
pub mod diff;
pub mod litnum_bound;
pub mod litnum_rewrite;

use crate::{elaborator::VdBsqElaboratorInner, *};

#[derive(Debug, PartialEq, Eq)]
pub enum VdBsqManeuver {
    Diff,
    LitnumRewrite,
    CacheTrivialBounds,
    LitnumBound,
}

#[derive(Debug, PartialEq, Eq)]
pub enum VdBsqManeuverCall {
    Diff,
    LitnumRewrite,
    TrivialBounds,
    LitnumBound,
}

impl VdBsqManeuverCall {
    pub fn wrap<'db, 'sess, R>(self, m: impl ElabM<'db, 'sess, R>) -> impl ElabM<'db, 'sess, R>
    where
        'db: 'sess,
    {
        call::stack::with_call(self, m)
    }
}
