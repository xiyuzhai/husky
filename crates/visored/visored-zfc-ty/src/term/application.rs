use super::{VdZfcTerm, VdZfcTermData, VdZfcTermId, ZfcTerms};

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VdZfcApplication(VdZfcTermId);

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VdZfcApplicationData {
    pub function: VdZfcTerm,
    pub arguments: ZfcTerms,
}

impl VdZfcApplication {
    pub fn data(self, db: &::salsa::Db) -> &VdZfcApplicationData {
        match self.0.data(db) {
            VdZfcTermData::Application(data) => data,
            _ => unreachable!(),
        }
    }
}
