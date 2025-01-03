pub mod builder;
pub mod coercion;
pub mod elaborator;
pub mod expr;
pub mod helpers;
pub mod hint;
pub mod hypothesis;
pub mod pattern;
pub mod region;
pub mod source_map;
pub mod stmt;
pub mod symbol;
pub mod tactic;
#[cfg(test)]
mod tests;

use self::builder::VdMirExprBuilder;
#[cfg(test)]
use self::tests::*;
use either::*;
use visored_models::VdModels;

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
