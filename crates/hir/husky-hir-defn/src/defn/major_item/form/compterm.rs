use super::*;
use husky_hir_decl::decl::major_item::form::compterm::MajorComptermHirDecl;
use husky_hir_expr::helpers::hir_body_with_expr_region;

#[salsa::interned(constructor = new_inner)]
pub struct MajorComptermHirDefn {
    pub path: MajorFormPath,
    pub hir_decl: MajorComptermHirDecl,
    pub hir_expr_body_and_region: Option<(HirExprIdx, HirExprRegion)>,
}

impl From<MajorComptermHirDefn> for MajorItemHirDefn {
    fn from(hir_defn: MajorComptermHirDefn) -> Self {
        MajorItemHirDefn::Form(hir_defn.into())
    }
}

impl From<MajorComptermHirDefn> for HirDefn {
    fn from(hir_defn: MajorComptermHirDefn) -> Self {
        HirDefn::MajorItem(hir_defn.into())
    }
}

impl MajorComptermHirDefn {
    pub(super) fn new(
        db: &::salsa::Db,
        path: MajorFormPath,
        hir_decl: MajorComptermHirDecl,
    ) -> Self {
        Self::new_inner(
            db,
            path,
            hir_decl,
            hir_body_with_expr_region(path.into(), db),
        )
    }

    pub fn hir_expr_region(self, db: &::salsa::Db) -> Option<HirExprRegion> {
        self.hir_expr_body_and_region(db).map(|v| v.1)
    }

    pub(super) fn deps(self, db: &::salsa::Db) -> HirDefnDeps {
        major_const_hir_defn_deps(db, self)
    }

    pub(super) fn version_stamp(self, db: &::salsa::Db) -> HirDefnVersionStamp {
        major_const_hir_defn_version_stamp(db, self)
    }
}

#[salsa::tracked]
fn major_const_hir_defn_deps(db: &::salsa::Db, hir_defn: MajorComptermHirDefn) -> HirDefnDeps {
    let mut builder = HirDefnDepsBuilder::new(hir_defn.path(db), db);
    let hir_decl = hir_defn.hir_decl(db);
    builder.add_hir_eager_expr_region(hir_decl.hir_eager_expr_region(db));
    builder.add_hir_ty(hir_decl.return_ty(db));
    if let Some(hir_expr_region) = hir_defn.hir_expr_region(db) {
        builder.add_hir_expr_region(hir_expr_region);
    }
    builder.finish()
}

#[salsa::tracked]
fn major_const_hir_defn_version_stamp(
    db: &::salsa::Db,
    hir_defn: MajorComptermHirDefn,
) -> HirDefnVersionStamp {
    HirDefnVersionStamp::new(hir_defn, db)
}
