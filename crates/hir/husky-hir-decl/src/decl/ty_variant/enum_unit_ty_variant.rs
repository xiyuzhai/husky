use super::*;
use husky_syn_decl::decl::ty_variant::unit_ty_variant::TypeUnitVariantSynDecl;

#[salsa::interned]
pub struct EnumUnitTypeVariantHirDecl {
    pub path: TypeVariantPath,
    pub hir_eager_expr_region: HirEagerExprRegion,
}

impl EnumUnitTypeVariantHirDecl {
    pub(super) fn from_syn(
        path: TypeVariantPath,
        syn_decl: TypeUnitVariantSynDecl,
        db: &::salsa::Db,
    ) -> Self {
        let builder = HirDeclBuilder::new(syn_decl.syn_expr_region(db), db);
        Self::new(db, path, builder.finish().eager())
    }
}
