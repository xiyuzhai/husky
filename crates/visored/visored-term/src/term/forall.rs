use super::*;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct VdForAll(VdTermId);

impl std::ops::Deref for VdForAll {
    type Target = VdTermId;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VdForAllData {
    // Add appropriate fields here
}

impl VdForAll {
    pub fn data(&self) -> &VdForAllData {
        match self.0.data() {
            VdTermData::ForAll(data) => data,
            _ => unreachable!(),
        }
    }
}
