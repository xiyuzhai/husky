use super::{VdTerm, VdTermData, VdTermId, ZfcTerms};

#[salsa::derive_debug_with_db]
#[salsa::as_id]
#[salsa::deref_id]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VdAbstraction(VdTermId);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VdAbstractionData {
    pub parameters: VdTerm,
    pub arguments: ZfcTerms,
}

impl VdAbstraction {
    pub fn data(self, db: &::salsa::Db) -> &VdAbstractionData {
        match self.0.data(db) {
            VdTermData::Abstraction(data) => data,
            _ => unreachable!(),
        }
    }
}
