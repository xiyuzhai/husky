use super::*;

#[salsa::derive_debug_with_db]
#[salsa::as_id]
#[salsa::deref_id]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VdLimit(VdTermId);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VdLimitData {
    // Add appropriate fields here
}

impl VdLimit {
    pub fn data(self, db: &::salsa::Db) -> &VdLimitData {
        match self.0.data(db) {
            VdTermData::Limit(data) => data,
            _ => unreachable!(),
        }
    }
}
