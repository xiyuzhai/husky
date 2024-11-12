mod builder;
pub mod clause;
pub mod division;
pub mod error;
pub mod expr;
pub mod helpers;
pub mod jar;
pub mod phrase;
pub mod range;
pub mod region;
pub mod sentence;
pub mod stmt;
pub mod symbol;
#[cfg(feature = "test_helpers")]
pub mod test_helpers;
#[cfg(test)]
mod tests;

use self::jar::VdSemExprJar as Jar;
#[cfg(test)]
use self::tests::*;
use builder::VdSemExprBuilder;
use either::*;
use expr::VdSemExprIdx;
use stmt::VdSemStmtIdxRange;
use visored_syn_expr::{expr::VdSynExprIdx, stmt::VdSynStmtIdxRange};

pub trait ToVdSem<T> {
    fn to_vd_sem(self, builder: &mut VdSemExprBuilder) -> T;
}

impl<L, R, T, S> ToVdSem<Either<T, S>> for Either<L, R>
where
    L: ToVdSem<T>,
    R: ToVdSem<S>,
{
    fn to_vd_sem(self, builder: &mut VdSemExprBuilder) -> Either<T, S> {
        match self {
            Left(left) => Left(left.to_vd_sem(builder)),
            Right(right) => Right(right.to_vd_sem(builder)),
        }
    }
}
