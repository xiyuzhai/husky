use super::*;

#[salsa::derive_debug_with_db]
#[salsa::as_id]
#[salsa::deref_id]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VdStackVariable(VdTermId);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VdStackVariableData {
    // Add appropriate fields here
}

impl VdStackVariable {
    pub fn data(self, db: &::salsa::Db) -> &VdStackVariableData {
        match self.0.data(db) {
            VdTermData::StackVariable(data) => data,
            _ => unreachable!(),
        }
    }
}
