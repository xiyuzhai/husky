#![feature(let_chains, if_let_guard)]
pub mod block;
mod builder;
pub mod clause;
pub mod division;
pub mod entity_tree;
pub mod error;
pub mod expr;
pub mod helpers;
pub mod parser;
pub mod pattern;
pub mod phrase;
pub mod range;
pub mod region;
pub mod sentence;
pub mod stmt;
pub mod symbol;
#[cfg(test)]
mod tests;

#[cfg(test)]
use self::tests::*;
use crate::builder::ToVdSyn;
use builder::VdSynExprBuilder;
use clause::VdSynClauseArena;
use division::VdSynDivisionArena;
use either::*;
use expr::{VdSynExprArena, VdSynExprIdx};
use latex_ast::{ast::LxAstArenaRef, range::LxAstTokenIdxRangeMap};
use latex_token::storage::LxTokenStorage;
use phrase::VdSynPhraseArena;
use sentence::VdSynSentenceArena;
use smallvec::SmallVec;
use stmt::VdSynStmtArena;
use visored_annotation::annotations::VdAnnotations;
use visored_global_resolution::default_table::VdDefaultGlobalResolutionTable;
