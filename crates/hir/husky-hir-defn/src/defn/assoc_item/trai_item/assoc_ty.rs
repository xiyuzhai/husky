use super::*;
use husky_hir_decl::decl::TraitAssocTypeHirDecl;

#[salsa::interned(db = HirDefnDb, jar = HirDefnJar, constructor = new_inner)]
pub struct TraitAssocTypeHirDefn {
    pub path: TraitItemPath,
    pub hir_decl: TraitAssocTypeHirDecl,
    pub hir_expr_region: HirEagerExprRegion,
    pub hir_eager_expr_region: Option<HirEagerExprRegion>,
}

impl From<TraitAssocTypeHirDefn> for AssocItemHirDefn {
    fn from(hir_defn: TraitAssocTypeHirDefn) -> Self {
        AssocItemHirDefn::TraitItem(hir_defn.into())
    }
}

impl From<TraitAssocTypeHirDefn> for HirDefn {
    fn from(hir_defn: TraitAssocTypeHirDefn) -> Self {
        HirDefn::AssocItem(hir_defn.into())
    }
}

impl TraitAssocTypeHirDefn {
    pub(super) fn dependencies(self, db: &::salsa::Db) -> HirDefnDependencies {
        trai_assoc_ty_hir_defn_dependencies(db, self)
    }

    pub(super) fn version_stamp(self, db: &::salsa::Db) -> HirDefnVersionStamp {
        trai_assoc_ty_hir_defn_version_stamp(db, self)
    }
}

#[salsa::tracked(jar = HirDefnJar)]
fn trai_assoc_ty_hir_defn_dependencies(
    db: &::salsa::Db,
    hir_defn: TraitAssocTypeHirDefn,
) -> HirDefnDependencies {
    let mut builder = HirDefnDependenciesBuilder::new(hir_defn.path(db), db);
    let hir_decl = hir_defn.hir_decl(db);
    builder.add_item_path(hir_decl.path(db).trai_path(db));
    builder.add_hir_eager_expr_region(hir_decl.hir_eager_expr_region(db));
    builder.add_hir_ty(hir_decl.ty(db));
    if let Some(hir_eager_expr_region) = hir_defn.hir_eager_expr_region(db) {
        builder.add_hir_eager_expr_region(hir_eager_expr_region);
    }
    builder.finish()
}

#[salsa::tracked(jar = HirDefnJar)]
fn trai_assoc_ty_hir_defn_version_stamp(
    db: &::salsa::Db,
    hir_defn: TraitAssocTypeHirDefn,
) -> HirDefnVersionStamp {
    HirDefnVersionStamp::new(hir_defn, db)
}