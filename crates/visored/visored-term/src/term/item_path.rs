use super::*;

#[salsa::derive_debug_with_db]
#[salsa::as_id]
#[salsa::deref_id]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VdItemPathTerm(VdTermId);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VdItemPathTermData {
    item_path: VdItemPath,
}

impl VdItemPathTermData {
    pub fn item_path(&self) -> VdItemPath {
        self.item_path
    }
}

impl VdTerm {
    pub fn new_item_path(item_path: VdItemPath, db: &::salsa::Db) -> Self {
        VdItemPathTerm(VdTermId::new(db, VdItemPathTermData { item_path }.into())).into()
    }
}
