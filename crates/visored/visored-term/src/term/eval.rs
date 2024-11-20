use super::*;

#[salsa::derive_debug_with_db]
#[salsa::as_id]
#[salsa::deref_id]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VdEval(VdTermId);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VdEvalData {
    // Add appropriate fields here
}

impl VdEval {
    pub fn data(self, db: &::salsa::Db) -> &VdEvalData {
        match self.0.data(db) {
            VdTermData::Eval(data) => data,
            _ => unreachable!(),
        }
    }
}
