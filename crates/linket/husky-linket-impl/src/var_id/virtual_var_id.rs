use super::*;

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct VirtualVarId;

impl IsVarId for () {
    fn generalize(self) -> Option<Self> {
        None
    }

    fn specialize(self, raw_id: u32) -> Self {
        unreachable!("reached max level of specialization")
    }
}
