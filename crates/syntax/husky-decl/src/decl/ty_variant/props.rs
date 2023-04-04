use crate::*;

#[salsa::tracked(db = DeclDb, jar = DeclJar)]
pub struct PropsVariantDecl {
    #[id]
    pub path: TypeVariantPath,
    pub expr_region: ExprRegion,
}