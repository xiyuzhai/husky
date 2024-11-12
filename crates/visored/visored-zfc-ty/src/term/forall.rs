use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VdZfcForAll(VdZfcTermId);

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VdZfcForAllData {
    // Add appropriate fields here
}

impl VdZfcForAll {
    pub fn data(self, db: &::salsa::Db) -> &VdZfcForAllData {
        match self.0.data(db) {
            VdZfcTermData::ForAll(data) => data,
            _ => unreachable!(),
        }
    }
}
