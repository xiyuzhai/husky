use crate::idx::LxTokenIdxRange;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum LxTokenLane {
    Main,
    Annotation(LxTokenAnnotationLane),
}

#[salsa::interned]
pub struct LxTokenAnnotationLane {
    pub token_idx_range: LxTokenIdxRange,
    pub channel: LxTokenAnnotationChannel,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum LxTokenAnnotationChannel {}
