pub mod error;
pub mod region;
pub mod signature;
pub mod term;

use self::error::SemExprHtmxResult;
use crate::*;
use either::*;
use husky_entity_path::path::major_item::ty::PreludeTypePath;
use husky_eth_term::term::{
    abstract_variable::EthAbstractVariable, symbolic_variable::EthSymbolicVariable, EthTerm,
};
use husky_term_prelude::ItemPathTerm;
use husky_visual_protocol::plot::PlotClass;
