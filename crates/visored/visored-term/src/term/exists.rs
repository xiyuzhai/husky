use super::*;

#[salsa::derive_debug_with_db]
#[salsa::as_id]
#[salsa::deref_id]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VdExists(VdTermId);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VdExistsData {
    // Add appropriate fields here
}

impl VdExists {
    pub fn data(self, db: &::salsa::Db) -> &VdExistsData {
        match self.0.data(db) {
            VdTermData::Exists(data) => data,
            _ => unreachable!(),
        }
    }
}
