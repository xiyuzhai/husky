use super::*;
use husky_hir_decl::decl::TypeAssocRitchieHirDecl;

#[salsa::interned(constructor = new_inner)]
pub struct TypeAssocRitchieHirDefn {
    pub path: TypeItemPath,
    pub hir_decl: TypeAssocRitchieHirDecl,
    pub eager_body_with_hir_eager_expr_region: Option<(HirEagerExprIdx, HirEagerExprRegion)>,
}

impl From<TypeAssocRitchieHirDefn> for AssocItemHirDefn {
    fn from(hir_defn: TypeAssocRitchieHirDefn) -> Self {
        AssocItemHirDefn::TypeItem(hir_defn.into())
    }
}

impl From<TypeAssocRitchieHirDefn> for HirDefn {
    fn from(hir_defn: TypeAssocRitchieHirDefn) -> Self {
        HirDefn::AssocItem(hir_defn.into())
    }
}

impl TypeAssocRitchieHirDefn {
    pub(super) fn new(
        db: &::salsa::Db,
        path: TypeItemPath,
        hir_decl: TypeAssocRitchieHirDecl,
    ) -> TypeAssocRitchieHirDefn {
        TypeAssocRitchieHirDefn::new_inner(
            db,
            path,
            hir_decl,
            hir_eager_body_with_expr_region(path.into(), db),
        )
    }

    pub fn hir_eager_expr_region(self, db: &::salsa::Db) -> Option<HirEagerExprRegion> {
        Some(self.eager_body_with_hir_eager_expr_region(db)?.1)
    }

    pub(super) fn deps(self, db: &::salsa::Db) -> HirDefnDeps {
        ty_assoc_ritchie_hir_defn_deps(db, self)
    }

    pub(super) fn version_stamp(self, db: &::salsa::Db) -> HirDefnVersionStamp {
        ty_assoc_ritchie_hir_defn_version_stamp(db, self)
    }
}

#[salsa::tracked]
fn ty_assoc_ritchie_hir_defn_deps(
    db: &::salsa::Db,
    hir_defn: TypeAssocRitchieHirDefn,
) -> HirDefnDeps {
    let mut builder = HirDefnDepsBuilder::new(hir_defn.path(db), db);
    let hir_decl = hir_defn.hir_decl(db);
    builder.add_item_path(hir_decl.path(db).impl_block(db));
    builder.add_hir_eager_expr_region(hir_decl.hir_eager_expr_region(db));
    for param in hir_decl.parenate_parameters(db).iter() {
        match *param {
            HirEagerParenateParameter::Simple { ty, .. } => builder.add_hir_ty(ty),
            HirEagerParenateParameter::Keyed => todo!(),
            HirEagerParenateParameter::Variadic => todo!(),
        }
    }
    builder.add_hir_ty(hir_decl.return_ty(db));
    if let Some(hir_eager_expr_region) = hir_defn.hir_eager_expr_region(db) {
        builder.add_hir_eager_expr_region(hir_eager_expr_region);
    }
    builder.finish()
}

#[salsa::tracked]
fn ty_assoc_ritchie_hir_defn_version_stamp(
    db: &::salsa::Db,
    hir_defn: TypeAssocRitchieHirDefn,
) -> HirDefnVersionStamp {
    HirDefnVersionStamp::new(hir_defn, db)
}
