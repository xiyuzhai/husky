pub mod menu;
pub mod signature;
pub mod table;
#[cfg(test)]
mod tests;

#[cfg(test)]
use self::tests::*;
#[cfg(test)]
use expect_test::*;
use visored_term::{instantiation::*, term::*, ty::*, *};
