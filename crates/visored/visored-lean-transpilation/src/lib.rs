mod builder;
mod coercion;
pub mod derivation;
pub mod dictionary;
mod expr;
pub mod helpers;
pub mod hypothesis;
pub mod mangle;
pub mod namespace;
pub mod scheme;
pub mod stmt;
#[cfg(test)]
mod tests;
pub mod ty;

use self::builder::VdLeanTranspilationBuilder;
use self::scheme::IsVdLeanTranspilationScheme;
#[cfg(test)]
use self::tests::*;
use either::Either;
use visored_models::VdModels;

pub trait VdTranspileToLean<S, T>: Copy
where
    S: IsVdLeanTranspilationScheme,
{
    fn to_lean(self, builder: &mut VdLeanTranspilationBuilder<S>) -> T;
}
