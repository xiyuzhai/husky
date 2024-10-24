// ! `husky-sem-expr`
#![feature(result_flattening)]
#![feature(let_chains)]
#![feature(if_let_guard)]
#![feature(const_trait_impl)]
#![allow(unused, warnings)]
#![feature(impl_trait_in_assoc_type)]
mod builder;
mod error;
pub mod expr;
pub mod jar;
// mod info;
pub mod helpers;
pub mod htmx;
pub mod obelisks;
pub mod pattern;
pub mod region;
pub mod stmt;
#[cfg(test)]
mod tests;

pub use self::builder::*;
pub use self::error::*;
pub use self::expr::*;
pub use self::jar::*;
pub use self::region::*;
pub use self::stmt::*;

use self::jar::SemExprJar as Jar;
use self::obelisks::*;
use either::*;
use husky_dec_signature::*;
use husky_entity_kind::*;
use husky_entity_path::*;
use husky_eth_term::*;
use husky_fly_term::*;
use husky_syn_defn::*;
use husky_syn_expr::{
    context::*, error::*, expr::*, parser::*, pattern::*, range::*, region::*, stmt::*,
    syndicates::*, variable::*,
};
use husky_term_prelude::*;
use salsa::DebugWithDb;
use smallvec::*;
#[cfg(test)]
use tests::*;
