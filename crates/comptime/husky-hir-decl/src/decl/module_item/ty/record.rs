use super::*;

#[salsa::interned(db = HirDeclDb, jar = HirDeclJar)]
pub struct RecordHirDecl {
    pub path: TypePath,
    #[return_ref]
    pub generic_parameters: EtherealGenericParameters,
}