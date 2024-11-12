use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LazyLoopRangeTracePath(TracePath);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LazyLoopRangeTracePathData {}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LazyLoopRangeTraceData {
    biological_parent: Trace,
}

impl LazyLoopRangeTraceData {
    pub fn biological_parent(&self) -> Trace {
        self.biological_parent
    }
}
