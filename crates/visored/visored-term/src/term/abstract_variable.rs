use super::*;

#[salsa::derive_debug_with_db]
#[salsa::as_id]
#[salsa::deref_id]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VdAbstractVariable(VdTermId);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VdAbstractVariableData {
    // Add appropriate fields here
}

impl VdAbstractVariable {
    pub fn data(self, db: &::salsa::Db) -> &VdAbstractVariableData {
        match self.0.data(db) {
            VdTermData::AbstractVariable(data) => data,
            _ => unreachable!(),
        }
    }
}
