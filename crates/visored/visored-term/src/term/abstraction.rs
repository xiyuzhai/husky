use super::{VdTerm, VdTermData, VdTermId, ZfcTerms};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct VdAbstraction(VdTermId);

impl std::ops::Deref for VdAbstraction {
    type Target = VdTermId;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VdAbstractionData {
    pub parameters: VdTerm,
    pub arguments: ZfcTerms,
}

impl VdAbstraction {
    pub fn data(&self) -> &VdAbstractionData {
        match self.0.data() {
            VdTermData::Abstraction(data) => data,
            _ => unreachable!(),
        }
    }
}
