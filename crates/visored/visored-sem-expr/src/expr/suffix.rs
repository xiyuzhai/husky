use super::*;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdSemSuffixOpr {
    Base(LxTokenIdxRange, VdBaseSuffixOpr),
    Composite(VdSemExprIdx, VdCompositeSuffixOpr),
}
