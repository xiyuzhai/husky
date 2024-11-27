use crate::idx::LxTokenIdxRange;

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum LxTokenLane {
    Main,
    Annotation(LxTokenAnnotationLane),
}

#[interned::interned]
pub struct LxTokenAnnotationLane {
    pub token_idx_range: LxTokenIdxRange,
    pub channel: LxTokenAnnotationChannel,
}

impl std::fmt::Debug for LxTokenAnnotationLane {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum LxTokenAnnotationChannel {}
