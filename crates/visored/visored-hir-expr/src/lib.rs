pub mod builder;
pub mod expr;
pub mod helpers;
pub mod jar;
pub mod region;
pub mod stmt;
#[cfg(feature = "test_helpers")]
pub mod test_helpers;
#[cfg(test)]
mod tests;

use self::builder::VdHirExprBuilder;
use self::jar::VdHirExprJar as Jar;
#[cfg(test)]
use self::tests::*;
use either::*;

pub trait ToVdHir<T>: Copy {
    fn to_vd_hir(self, builder: &mut VdHirExprBuilder) -> T;
}

impl<L, R, S, T> ToVdHir<Either<S, T>> for Either<L, R>
where
    L: ToVdHir<S>,
    R: ToVdHir<T>,
{
    fn to_vd_hir(self, builder: &mut VdHirExprBuilder) -> Either<S, T> {
        match self {
            Either::Left(l) => Either::Left(l.to_vd_hir(builder)),
            Either::Right(r) => Either::Right(r.to_vd_hir(builder)),
        }
    }
}
