pub mod builder;
pub mod expr;
pub mod helpers;
pub mod jar;
pub mod pattern;
pub mod region;
pub mod stmt;
pub mod symbol;
#[cfg(test)]
mod tests;

use self::builder::VdMirExprBuilder;
use self::jar::VdMirExprJar as Jar;
#[cfg(test)]
use self::tests::*;
use either::*;

pub trait ToVdMir<T>: Copy {
    fn to_vd_mir(self, builder: &mut VdMirExprBuilder) -> T;
}

impl<L, R, S, T> ToVdMir<Either<S, T>> for Either<L, R>
where
    L: ToVdMir<S>,
    R: ToVdMir<T>,
{
    fn to_vd_mir(self, builder: &mut VdMirExprBuilder) -> Either<S, T> {
        match self {
            Either::Left(l) => Either::Left(l.to_vd_mir(builder)),
            Either::Right(r) => Either::Right(r.to_vd_mir(builder)),
        }
    }
}
