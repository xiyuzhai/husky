pub mod assoc_ritchie;
pub mod assoc_ty;
pub mod assoc_val;
pub mod method_ritchie;

use self::assoc_ritchie::*;
use self::assoc_ty::*;
use self::assoc_val::*;
use self::method_ritchie::*;
use super::*;
use husky_entity_path::path::assoc_item::trai_item::TraitItemPath;
use husky_hir_decl::decl::TraitItemHirDecl;

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
#[salsa::derive_debug_with_db]
#[enum_class::from_variants]
pub enum TraitItemHirDefn {
    AssocRitchie(TraitAssocRitchieHirDefn),
    MethodFn(TraitMethodFnHirDefn),
    AssocType(TraitAssocTypeHirDefn),
    AssocVal(TraitAssocValHirDefn),
}

impl From<TraitItemHirDefn> for HirDefn {
    fn from(hir_defn: TraitItemHirDefn) -> Self {
        HirDefn::AssocItem(hir_defn.into())
    }
}

impl TraitItemHirDefn {
    pub fn hir_decl(self, _db: &::salsa::Db) -> TraitItemHirDecl {
        todo!()
    }

    pub fn path(self, _db: &::salsa::Db) -> AssocItemPath {
        todo!()
    }
    pub fn hir_expr_region(self, _db: &::salsa::Db) -> HirExprRegion {
        todo!()
    }

    pub(super) fn deps(self, db: &::salsa::Db) -> HirDefnDeps {
        match self {
            TraitItemHirDefn::AssocRitchie(hir_defn) => hir_defn.deps(db),
            TraitItemHirDefn::MethodFn(hir_defn) => hir_defn.deps(db),
            TraitItemHirDefn::AssocType(hir_defn) => hir_defn.deps(db),
            TraitItemHirDefn::AssocVal(hir_defn) => hir_defn.deps(db),
        }
    }

    pub(super) fn version_stamp(self, db: &::salsa::Db) -> HirDefnVersionStamp {
        match self {
            TraitItemHirDefn::AssocRitchie(hir_defn) => hir_defn.version_stamp(db),
            TraitItemHirDefn::MethodFn(hir_defn) => hir_defn.version_stamp(db),
            TraitItemHirDefn::AssocType(hir_defn) => hir_defn.version_stamp(db),
            TraitItemHirDefn::AssocVal(hir_defn) => hir_defn.version_stamp(db),
        }
    }
}

impl HasHirDefn for TraitItemPath {
    type HirDefn = TraitItemHirDefn;

    fn hir_defn(self, db: &::salsa::Db) -> Option<Self::HirDefn> {
        trai_item_hir_defn(db, self)
    }
}

#[salsa::tracked]
pub(crate) fn trai_item_hir_defn(
    db: &::salsa::Db,
    path: TraitItemPath,
) -> Option<TraitItemHirDefn> {
    let hir_decl = path.hir_decl(db)?;
    match hir_decl {
        TraitItemHirDecl::AssocRitchie(_hir_decl) => {
            todo!()
            // TraitAssocRitchieHirDefn::new(db, path, hir_decl)?.into()
        }
        TraitItemHirDecl::MethodFn(hir_decl) => {
            Some(TraitMethodFnHirDefn::new(db, path, hir_decl).into())
        }
        TraitItemHirDecl::AssocType(_hir_decl) => todo!(),
        TraitItemHirDecl::AssocVal(_hir_decl) => todo!(),
    }
}
