mod builder;
pub mod dictionary;
mod expr;
pub mod helpers;
pub mod mangle;
pub mod namespace;
pub mod stmt;
#[cfg(test)]
mod tests;
pub mod ty;

use self::builder::VdLeanTranspilationBuilder;
#[cfg(test)]
use self::tests::*;

pub trait VdTranspileToLean<T>: Copy {
    fn to_lean(self, builder: &mut VdLeanTranspilationBuilder) -> T;
}
