use super::*;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct VdItemPathTerm(VdTermId);

impl std::ops::Deref for VdItemPathTerm {
    type Target = VdTermId;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VdItemPathTermData {
    item_path: VdItemPath,
}

impl VdItemPathTermData {
    pub fn item_path(&self) -> VdItemPath {
        self.item_path
    }
}

impl VdItemPathTerm {
    pub fn new(item_path: VdItemPath) -> Self {
        VdItemPathTerm(VdTermId::new(VdItemPathTermData { item_path }.into())).into()
    }
}

impl VdTerm {
    pub fn new_item_path(item_path: VdItemPath) -> Self {
        VdTerm::ItemPath(VdItemPathTerm::new(item_path))
    }
}
