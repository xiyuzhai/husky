use super::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VdZfcStackVariable(VdZfcTermId);

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VdZfcStackVariableData {
    // Add appropriate fields here
}

impl VdZfcStackVariable {
    pub fn data(self, db: &::salsa::Db) -> &VdZfcStackVariableData {
        match self.0.data(db) {
            VdZfcTermData::StackVariable(data) => data,
            _ => unreachable!(),
        }
    }
}
