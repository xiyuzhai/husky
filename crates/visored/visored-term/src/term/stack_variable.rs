use super::*;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VdStackVariable(VdTermId);

impl std::ops::Deref for VdStackVariable {
    type Target = VdTermId;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VdStackVariableData {
    // Add appropriate fields here
}

impl VdStackVariable {
    pub fn data(self) -> &'static VdStackVariableData {
        match self.0.data() {
            VdTermData::StackVariable(data) => data,
            _ => unreachable!(),
        }
    }
}
