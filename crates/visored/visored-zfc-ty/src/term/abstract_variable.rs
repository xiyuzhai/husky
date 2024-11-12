use super::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VdZfcAbstractVariable(VdZfcTermId);

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VdZfcAbstractVariableData {
    // Add appropriate fields here
}

impl VdZfcAbstractVariable {
    pub fn data(self, db: &::salsa::Db) -> &VdZfcAbstractVariableData {
        match self.0.data(db) {
            VdZfcTermData::AbstractVariable(data) => data,
            _ => unreachable!(),
        }
    }
}
