#![feature(let_chains)]
//! this crate renders the trace doc, which displays the traces and their peripheries
pub mod doc;
mod facade;
pub mod helpers;
pub mod hotkey;
pub mod settings;
mod view;

use self::settings::*;
use husky_trace_protocol::{caryatid::IsCaryatid, view::action::TraceViewAction};
use serde::{Deserialize, Serialize};
