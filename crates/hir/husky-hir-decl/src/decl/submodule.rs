use super::*;
use husky_entity_path::path::submodule::SubmoduleItemPath;

#[salsa::interned(constructor = new)]
pub struct SubmoduleHirDecl {
    pub path: SubmoduleItemPath,
}

impl HasHirDecl for SubmoduleItemPath {
    type HirDecl = SubmoduleHirDecl;

    fn hir_decl(self, db: &::salsa::Db) -> Option<Self::HirDecl> {
        Some(submodule_hir_decl(db, self))
    }
}

#[salsa::tracked]
fn submodule_hir_decl(db: &::salsa::Db, path: SubmoduleItemPath) -> SubmoduleHirDecl {
    SubmoduleHirDecl::new(db, path)
}
