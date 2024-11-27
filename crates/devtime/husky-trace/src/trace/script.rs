use super::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ScriptTracePathData {
    biological_parent_path: TracePath,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScriptTraceData {
    biological_parent: Trace,
    source: String,
}

impl ScriptTraceData {
    pub fn biological_parent(&self) -> Trace {
        self.biological_parent
    }
}
