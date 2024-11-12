pub mod caryatid;
pub mod chart;
pub mod figure;

use self::caryatid::*;
use self::figure::StandardFigure;
use husky_standard_linket_impl::{pedestal::StandardPedestal, var::StandardVarId};
use husky_trace_protocol::{figure::IsFigure, protocol::IsTraceProtocol};
use serde::{Deserialize, Serialize};
use std::marker::PhantomData;

#[derive(Debug, Serialize, Deserialize, PartialEq, Eq, Clone)]
pub struct StandardTraceProtocol;

impl Default for StandardTraceProtocol {
    fn default() -> Self {
        Self
    }
}

impl IsTraceProtocol for StandardTraceProtocol {
    type Pedestal = StandardPedestal;

    type Caryatid = StandardCaryatid;

    type Figure = StandardFigure;
}
