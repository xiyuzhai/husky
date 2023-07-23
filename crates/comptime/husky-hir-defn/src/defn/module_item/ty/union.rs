use super::*;

#[salsa::tracked(db = HirDefnDb, jar = HirDefnJar)]
pub struct UnionTypeHirDefn {
    #[id]
    pub path: TypePath,
    pub decl: UnionTypeHirDecl,
}