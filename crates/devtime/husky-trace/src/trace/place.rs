use super::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PlaceTracePathData {
    biological_parent_path: TracePath,
    place_access: PlaceAccess,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PlaceAccess {
    StructField,
    EnumVariantField,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct PlaceTraceData {
    biological_parent: Trace,
}

impl PlaceTraceData {
    pub fn biological_parent(&self) -> Trace {
        self.biological_parent
    }
}
