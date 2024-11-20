pub mod table;

use smallvec::{smallvec, SmallVec};
use visored_coword::namae::VdNamae;
use visored_item_path::path::VdItemPath;

#[salsa::interned]
pub struct VdType {
    pub data: VdTypeData,
    pub refinements: SmallVec<[(); 2]>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VdTypeData {
    ItemPath(VdItemPath), // TODO: do we need a path here?
}

impl VdType {
    pub fn new_item_path(item_path: VdItemPath, db: &::salsa::Db) -> Self {
        VdType::new(db, VdTypeData::ItemPath(item_path).into(), smallvec![]).into()
    }
}

impl VdType {
    pub fn is_function_like(self, db: &::salsa::Db) -> bool {
        is_vd_ty_function_like(db, self)
    }
}

#[salsa::tracked]
fn is_vd_ty_function_like(db: &::salsa::Db, ty: VdType) -> bool {
    // TODO: ad hoc implementation
    match ty.data(db) {
        VdTypeData::ItemPath(vd_item_path) => false,
    }
}
