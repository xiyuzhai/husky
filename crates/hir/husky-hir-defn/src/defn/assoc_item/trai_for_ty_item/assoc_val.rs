use super::*;
use husky_hir_decl::decl::TraitForTypeAssocValHirDecl;

#[salsa::interned(constructor = new_inner)]
pub struct TraitForTypeAssocValHirDefn {
    pub path: TraitForTypeItemPath,
    pub hir_decl: TraitForTypeAssocValHirDecl,
    pub hir_expr_region: Option<HirExprRegion>,
}

impl From<TraitForTypeAssocValHirDefn> for AssocItemHirDefn {
    fn from(hir_defn: TraitForTypeAssocValHirDefn) -> Self {
        AssocItemHirDefn::TraitForTypeItem(hir_defn.into())
    }
}

impl From<TraitForTypeAssocValHirDefn> for HirDefn {
    fn from(hir_defn: TraitForTypeAssocValHirDefn) -> Self {
        HirDefn::AssocItem(hir_defn.into())
    }
}

impl TraitForTypeAssocValHirDefn {
    pub(super) fn new(
        _db: &::salsa::Db,
        _path: TraitForTypeItemPath,
        _hir_decl: TraitForTypeAssocValHirDecl,
    ) -> Self {
        todo!()
    }

    pub(super) fn deps(self, db: &::salsa::Db) -> HirDefnDeps {
        trai_for_ty_assoc_val_hir_defn_deps(db, self)
    }

    pub(super) fn version_stamp(self, db: &::salsa::Db) -> HirDefnVersionStamp {
        trai_for_ty_assoc_val_hir_defn_version_stamp(db, self)
    }
}

#[salsa::tracked]
fn trai_for_ty_assoc_val_hir_defn_deps(
    db: &::salsa::Db,
    hir_defn: TraitForTypeAssocValHirDefn,
) -> HirDefnDeps {
    let mut builder = HirDefnDepsBuilder::new(hir_defn.path(db), db);
    let hir_decl = hir_defn.hir_decl(db);
    builder.add_hir_expr_region(hir_decl.hir_expr_region(db));
    builder.add_item_path(hir_decl.path(db).impl_block(db));
    builder.add_hir_ty(hir_decl.return_ty(db));
    if let Some(hir_expr_region) = hir_defn.hir_expr_region(db) {
        builder.add_hir_expr_region(hir_expr_region);
    }
    builder.finish()
}

#[salsa::tracked]
fn trai_for_ty_assoc_val_hir_defn_version_stamp(
    db: &::salsa::Db,
    hir_defn: TraitForTypeAssocValHirDefn,
) -> HirDefnVersionStamp {
    HirDefnVersionStamp::new(hir_defn, db)
}
