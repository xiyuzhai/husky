use super::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VdZfcEval(VdZfcTermId);

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VdZfcEvalData {
    // Add appropriate fields here
}

impl VdZfcEval {
    pub fn data(self, db: &::salsa::Db) -> &VdZfcEvalData {
        match self.0.data(db) {
            VdZfcTermData::Eval(data) => data,
            _ => unreachable!(),
        }
    }
}
