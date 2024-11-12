#![feature(anonymous_lifetime_in_impl_trait)]
pub mod annotation;
pub mod annotations;
#[cfg(feature = "test_helpers")]
pub mod test_helpers;
#[cfg(test)]
mod tests;

#[cfg(test)]
use crate::tests::*;
