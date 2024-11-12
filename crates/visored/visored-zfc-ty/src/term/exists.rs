use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VdZfcExists(VdZfcTermId);

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VdZfcExistsData {
    // Add appropriate fields here
}

impl VdZfcExists {
    pub fn data(self, db: &::salsa::Db) -> &VdZfcExistsData {
        match self.0.data(db) {
            VdZfcTermData::Exists(data) => data,
            _ => unreachable!(),
        }
    }
}
