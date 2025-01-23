#![feature(if_let_guard)]
#![feature(never_type)]
#![feature(proc_macro_hygiene)]
#![feature(stmt_expr_attributes)]
#![feature(let_chains)]
pub mod call;
pub mod coercion;
pub mod config;
pub mod derivation;
mod elabm;
pub mod elaborator;
pub mod expr;
pub mod foundations;
pub mod helpers;
pub mod hypothesis;
pub mod maneuver;
pub mod outcome;
pub mod session;
mod signature;
pub mod strategy;
pub mod tactic;
pub mod term;
#[cfg(test)]
mod tests;
pub mod variable;

use crate::elabm::ElabM;
use alt_maybe_result::*;
use elaborator::VdBsqElaboratorInner;
use eterned::db::EternerDb;
use husky_control_flow_utils::require;
use husky_debug_utils::*;
use husky_print_utils::*;
use hypothesis::{contradiction::VdBsqHypothesisResult, VdBsqHypothesisIdx};
use miracle::error::MiracleAltMaybeResult;
use visored_models::VdModels;

type Elr<'db, 'sess> = VdBsqElaboratorInner<'db, 'sess>;
type Mhr<'sess> = MiracleAltMaybeResult<VdBsqHypothesisResult<'sess, VdBsqHypothesisIdx<'sess>>>;
type Hr<'sess> = VdBsqHypothesisResult<'sess, VdBsqHypothesisIdx<'sess>>;
type Heuristic<'a, 'db, 'sess, T> =
    dyn Fn(&mut VdBsqElaboratorInner<'db, 'sess>, T) -> Mhr<'sess> + 'a;
