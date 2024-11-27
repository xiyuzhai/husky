use crate::*;
use husky_entity_path::path::major_item::ty::TypePath;
use husky_syn_decl::decl::major_item::ty::structure::StructureSynDecl;

#[salsa::interned]
pub struct StructureTypeDecTemplate {
    #[return_ref]
    pub template_parameters: DecTemplateParameters,
}

impl StructureTypeDecTemplate {
    pub(super) fn from_decl(
        db: &::salsa::Db,
        path: TypePath,
        decl: StructureSynDecl,
    ) -> DecSignatureResult<Self> {
        let syn_expr_region = decl.syn_expr_region(db);
        let dec_term_region = syn_expr_dec_term_region(db, syn_expr_region);
        let dec_term_menu = db.dec_term_menu(syn_expr_region.toolchain(db)).unwrap();
        let template_parameters = DecTemplateParameters::from_decl(
            decl.template_parameters(db),
            &dec_term_region,
            dec_term_menu,
        );
        Ok(Self::new(db, template_parameters))
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
#[salsa::derive_debug_with_db]
pub struct StructureTypeDecSignature {}
