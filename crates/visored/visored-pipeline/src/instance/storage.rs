use super::*;
use idx_arena::Arena;

pub struct VdPipelineInstanceStorage {
    arena: Arena<VdPipelineInstance>,
}

impl VdPipelineInstanceStorage {
    pub(crate) fn new_empty() -> Self {
        Self {
            arena: Arena::default(),
        }
    }
}

impl VdPipelineInstanceStorage {
    pub fn alloc_instances(
        &mut self,
        instances: impl IntoIterator<Item = VdPipelineInstance>,
    ) -> VdPipelineInstanceIdxRange {
        self.arena.alloc_many(instances)
    }

    pub fn all_instances(&self) -> &[VdPipelineInstance] {
        &*self.arena.data()
    }

    pub(crate) fn all_instances_mut(&mut self) -> &mut [VdPipelineInstance] {
        unsafe { self.arena.data_mut() }
    }
}

impl std::ops::Index<VdPipelineInstanceIdx> for VdPipelineInstanceStorage {
    type Output = VdPipelineInstance;

    fn index(&self, idx: VdPipelineInstanceIdx) -> &Self::Output {
        &self.arena[idx]
    }
}
