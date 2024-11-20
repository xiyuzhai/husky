use super::*;

#[salsa::derive_debug_with_db]
#[salsa::as_id]
#[salsa::deref_id]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VdForAll(VdTermId);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VdForAllData {
    // Add appropriate fields here
}

impl VdForAll {
    pub fn data(self, db: &::salsa::Db) -> &VdForAllData {
        match self.0.data(db) {
            VdTermData::ForAll(data) => data,
            _ => unreachable!(),
        }
    }
}
