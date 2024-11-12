use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct EagerLoopFrameTracePath(TracePath);

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct EagerLoopFrameTracePathData {}

impl EagerLoopFrameTracePath {
    pub fn view_data(self, _db: &::salsa::Db) -> TraceViewData {
        todo!()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EagerLoopFrameTrace(Trace);

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EagerLoopFrameTraceData {
    path: EagerLoopFrameTracePath,
    biological_parent: Trace,
}

impl EagerLoopFrameTraceData {
    pub fn subtraces(self, _db: &::salsa::Db) -> &[Trace] {
        todo!()
    }

    pub fn var_deps(&self, trace: Trace, db: &::salsa::Db) -> TraceVarDeps {
        todo!()
    }

    pub fn var_deps_expansion(&self, db: &::salsa::Db) -> TraceVarDepsExpansion {
        todo!()
    }

    pub fn biological_parent(&self) -> Trace {
        self.biological_parent
    }
}
