use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LazyLoopFrameTracePath(TracePath);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LazyLoopFrameTracePathData {}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LazyLoopFrameTraceData {
    biological_parent: Trace,
}

impl LazyLoopFrameTraceData {
    pub fn biological_parent(&self) -> Trace {
        self.biological_parent
    }
}
