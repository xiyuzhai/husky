pub mod jar;
pub mod menu;
pub mod module;
pub mod namespace;
pub mod path;
#[cfg(test)]
mod tests;

use self::jar::VdItemPathJar as Jar;
#[cfg(test)]
use crate::tests::*;
