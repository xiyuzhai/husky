use super::{VdTerm, VdTermData, VdTermId, ZfcTerms};

#[salsa::derive_debug_with_db]
#[salsa::as_id]
#[salsa::deref_id]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VdApplication(VdTermId);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VdApplicationData {
    pub function: VdTerm,
    pub arguments: ZfcTerms,
}

impl VdApplication {
    pub fn data(self, db: &::salsa::Db) -> &VdApplicationData {
        match self.0.data(db) {
            VdTermData::Application(data) => data,
            _ => unreachable!(),
        }
    }
}
