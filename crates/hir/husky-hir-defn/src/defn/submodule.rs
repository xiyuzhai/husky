use super::*;
use husky_entity_path::path::submodule::SubmoduleItemPath;
use husky_hir_decl::decl::SubmoduleHirDecl;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[salsa::derive_debug_with_db]
pub struct SubmoduleHirDefn {
    hir_decl: SubmoduleHirDecl,
}

impl SubmoduleHirDefn {
    pub fn path(self, db: &::salsa::Db) -> SubmoduleItemPath {
        self.hir_decl.path(db)
    }

    pub fn hir_decl(self) -> SubmoduleHirDecl {
        self.hir_decl
    }
}

impl HasHirDefn for SubmoduleItemPath {
    type HirDefn = SubmoduleHirDefn;

    fn hir_defn(self, db: &::salsa::Db) -> Option<Self::HirDefn> {
        Some(SubmoduleHirDefn {
            hir_decl: self.hir_decl(db)?,
        })
    }
}
