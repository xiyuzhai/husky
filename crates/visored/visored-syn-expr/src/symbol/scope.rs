use super::*;
use latex_token::idx::LxTokenIdxRange;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VdSynSymbolScope {
    Simple { range: LxTokenIdxRange },
}
