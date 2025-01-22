#![feature(let_chains)]
#![feature(if_let_guard)]
pub mod builder;
pub mod coercion;
pub mod derivation;
pub mod division;
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

use self::builder::region::VdMirExprRegionBuilder;
#[cfg(test)]
use self::tests::*;
use either::*;
use husky_print_utils::*;
use visored_models::VdModels;

pub trait ToVdMir<T, Builder> {
    fn to_vd_mir(self, builder: &mut Builder) -> T;
}

impl<L, R, S, T, B> ToVdMir<Either<S, T>, B> for Either<L, R>
where
    L: ToVdMir<S, B>,
    R: ToVdMir<T, B>,
{
    fn to_vd_mir(self, builder: &mut B) -> Either<S, T> {
        match self {
            Either::Left(l) => Either::Left(l.to_vd_mir(builder)),
            Either::Right(r) => Either::Right(r.to_vd_mir(builder)),
        }
    }
}
