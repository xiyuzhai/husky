use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct EagerLoopRangeTracePath(TracePath);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct EagerLoopRangeTracePathData {}

impl EagerLoopRangeTracePath {
    pub fn view_data(self, _db: &::salsa::Db) -> TraceViewData {
        todo!()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EagerLoopGroupTrace(Trace);

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EagerLoopRangeTraceData {
    path: EagerLoopRangeTracePath,
    biological_parent: Trace,
}

impl EagerLoopRangeTraceData {
    pub fn biological_parent(&self) -> Trace {
        self.biological_parent
    }

    pub fn subtraces(self, _db: &::salsa::Db) -> &[Trace] {
        todo!()
    }

    pub fn var_deps(&self, trace: Trace, db: &::salsa::Db) -> TraceVarDeps {
        todo!()
    }

    pub fn var_deps_expansion(&self, db: &::salsa::Db) -> TraceVarDepsExpansion {
        todo!()
    }
}
