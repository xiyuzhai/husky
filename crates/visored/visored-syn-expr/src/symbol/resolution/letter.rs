use super::*;

#[enum_class::from_variants]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdSynLetterSymbolResolution {
    Global(VdLetterGlobalResolution),
    Local(VdSynSymbolLocalDefnIdx),
}
