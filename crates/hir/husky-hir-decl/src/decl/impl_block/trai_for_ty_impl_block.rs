use super::*;
use husky_entity_path::path::impl_block::trai_for_ty_impl_block::TraitForTypeImplBlockPath;
use husky_eth_signature::signature::HasEthTemplate;
use husky_hir_ty::trai::HirTrait;

#[salsa::interned(constructor = new)]
pub struct TraitForTypeImplBlockHirDecl {
    pub path: TraitForTypeImplBlockPath,
    #[return_ref]
    pub template_parameters: HirTemplateParameters,
    pub trai: HirTrait,
    pub self_ty: HirType,
    // todo: where clause
    pub hir_eager_expr_region: HirEagerExprRegion,
}

impl HasHirDecl for TraitForTypeImplBlockPath {
    type HirDecl = TraitForTypeImplBlockHirDecl;

    fn hir_decl(self, db: &::salsa::Db) -> Option<Self::HirDecl> {
        trai_for_ty_impl_block_hir_decl(db, self)
    }
}

#[salsa::tracked]
fn trai_for_ty_impl_block_hir_decl(
    db: &::salsa::Db,
    path: TraitForTypeImplBlockPath,
) -> Option<TraitForTypeImplBlockHirDecl> {
    let syn_decl = path.syn_decl(db).expect("ok");
    let builder = HirDeclBuilder::new(syn_decl.syn_expr_region(db), db);
    let template_parameters =
        HirTemplateParameters::from_syn(syn_decl.template_parameters(db), &builder);
    let signature_template = path.eth_template(db).unwrap();
    let trai = HirTrait::from_eth(signature_template.trai(db), db);
    let self_ty = HirType::from_eth(signature_template.self_ty(db), db).unwrap();
    Some(TraitForTypeImplBlockHirDecl::new(
        db,
        path,
        template_parameters,
        trai,
        self_ty,
        builder.finish().eager(),
    ))
}
