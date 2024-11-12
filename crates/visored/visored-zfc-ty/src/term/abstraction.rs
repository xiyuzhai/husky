use super::{VdZfcTerm, VdZfcTermData, VdZfcTermId, ZfcTerms};

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VdZfcAbstraction(VdZfcTermId);

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VdZfcAbstractionData {
    pub parameters: VdZfcTerm,
    pub arguments: ZfcTerms,
}

impl VdZfcAbstraction {
    pub fn data(self, db: &::salsa::Db) -> &VdZfcAbstractionData {
        match self.0.data(db) {
            VdZfcTermData::Abstraction(data) => data,
            _ => unreachable!(),
        }
    }
}
