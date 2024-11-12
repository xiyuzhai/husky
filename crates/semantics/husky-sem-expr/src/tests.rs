pub(crate) use husky_ast::test_helpers::*;

use crate::*;
use husky_vfs::path::module_path::ModulePath;

#[salsa::db(
    husky_coword::jar::CowordJar,
    husky_vfs::jar::VfsJar,
    husky_entity_path::jar::EntityPathJar,
    husky_token_data::jar::TokenDataJar,
    husky_token::jar::TokenJar,
    husky_ast::jar::AstJar,
    husky_text::jar::TextJar,
    husky_place::jar::PlaceJar,
    husky_entity_tree::jar::EntityTreeJar,
    husky_toml_token::jar::TomlTokenJar,
    husky_toml_ast::jar::TomlAstJar,
    husky_manifest_ast::jar::ManifestAstJar,
    husky_corgi_config::jar::CorgiConfigJar,
    husky_corgi_config_ast::jar::CorgiConfigAstJar,
    husky_manifest::jar::ManifestJar,
    husky_syn_expr::jar::SynExprJar,
    husky_syn_defn::jar::SynDefnJar,
    husky_syn_decl::jar::SynDeclJar,
    husky_term_prelude::jar::TermPreludeJar,
    husky_dec_term::jar::DecTermJar,
    husky_dec_signature::jar::DecSignatureJar,
    husky_dec_ty::jar::DecTypeJar,
    husky_eth_term::jar::EthTermJar,
    husky_eth_signature::jar::EthSignatureJar,
    husky_fly_term::jar::FlyTermJar,
    Jar
)]
#[derive(Default)]
pub(crate) struct DB;

fn decl_sem_expr_regions(db: &::salsa::Db, module_path: ModulePath) -> Vec<SemExprRegion> {
    use husky_syn_decl::sheet::HasSynDeclSheet;

    module_path
        .syn_decl_sheet(db)
        .decls(db)
        .iter()
        .copied()
        .filter_map(|(_, decl)| Some(db.sem_expr_region(decl.syn_expr_region(db)?)))
        .collect()
}

#[test]
fn decl_sem_expr_regions_works() {
    DB::ast_rich_test_debug_with_db(
        decl_sem_expr_regions,
        &AstTestConfig::new(
            "decl_sem_expr_regions",
            FileExtensionConfig::Markdown,
            TestDomainsConfig::SEMANTICS,
        ),
    )
}

fn defn_sem_expr_regions(db: &::salsa::Db, module_path: ModulePath) -> Vec<SemExprRegion> {
    module_item_syn_defns(db, module_path)
        .iter()
        .copied()
        .filter_map(|(_, defn)| Some(db.sem_expr_region(defn?.syn_expr_region)))
        .collect()
}

#[test]
fn defn_sem_expr_regions_works() {
    DB::ast_rich_test_debug_with_db(
        defn_sem_expr_regions,
        &AstTestConfig::new(
            "defn_sem_expr_regions",
            FileExtensionConfig::Markdown,
            TestDomainsConfig::SEMANTICS,
        ),
    )
}
