mod builder;
pub mod dictionary;
mod expr;
pub mod helpers;
pub mod jar;
pub mod stmt;
#[cfg(feature = "test_helpers")]
mod test_helpers;
#[cfg(test)]
mod tests;

#[cfg(test)]
use self::tests::*;
use self::{builder::VdLeanTranspilationBuilder, jar::VdLeanTranspilationJar as Jar};

pub trait TranspileToLean<T>: Copy {
    fn to_lean(self, builder: &mut VdLeanTranspilationBuilder) -> T;
}
