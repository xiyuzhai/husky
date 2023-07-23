use super::*;

#[salsa::interned(db = HirDeclDb, jar = HirDeclJar)]
pub struct UnitStructHirDecl {
    pub path: TypePath,
    #[return_ref]
    pub generic_parameters: EtherealGenericParameters,
}