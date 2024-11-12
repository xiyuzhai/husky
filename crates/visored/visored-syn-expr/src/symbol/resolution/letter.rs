use super::*;

#[enum_class::from_variants]
#[derive(Debug, PartialEq, Eq)]
pub enum VdSynLetterSymbolResolution {
    Global(VdLetterGlobalResolution),
    Local(VdSynSymbolLocalDefnIdx),
}
