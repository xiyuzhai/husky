use super::*;

#[salsa::tracked(db = HirDeclDb, jar = HirDeclJar)]
pub struct TypeAssociatedFnHirDecl {
    #[id]
    pub path: TypeItemPath,
    pub self_ty: EtherealTerm,
    pub generic_parameters: EtherealGenericParameters,
    pub parenic_parameters: ParenicEtherealParameters,
    pub return_ty: EtherealTerm,
    pub ty: EtherealTerm,
}