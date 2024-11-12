use super::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VdZfcLimit(VdZfcTermId);

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VdZfcLimitData {
    // Add appropriate fields here
}

impl VdZfcLimit {
    pub fn data(self, db: &::salsa::Db) -> &VdZfcLimitData {
        match self.0.data(db) {
            VdZfcTermData::Limit(data) => data,
            _ => unreachable!(),
        }
    }
}
