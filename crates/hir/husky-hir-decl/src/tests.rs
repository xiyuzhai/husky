pub(crate) use husky_ast::test_helpers::*;
use husky_vfs::path::module_path::ModulePath;

use crate::{jar::*, *};
use husky_corgi_config::jar::CorgiConfigJar;
use husky_corgi_config_ast::CorgiConfigAstJar;
use husky_coword::jar::CowordJar;
use husky_dec_signature::jar::DecSignatureJar;
use husky_entity_tree::{helpers::paths::module_item_paths, jar::EntityTreeJar};
use husky_eth_signature::jar::EthSignatureJar;
use husky_eth_term::jar::EthTermJar;
use husky_fly_term::jar::FlyTermJar;
use husky_manifest::jar::ManifestJar;
use husky_manifest_ast::jar::ManifestAstJar;
use husky_sem_expr::SemExprJar;
use husky_syn_decl::jar::SynDeclJar;
use husky_syn_defn::jar::SynDefnJar;
use husky_syn_expr::jar::SynExprJar;
use husky_term_prelude::jar::TermPreludeJar;
use husky_token::TokenJar;
use husky_toml_ast::TomlAstJar;

#[salsa::db(
    CowordJar,
    husky_vfs::jar::VfsJar,
    husky_entity_path::jar::EntityPathJar,
    husky_place::jar::PlaceJar,
    husky_text::jar::TextJar,
    husky_token_data::jar::TokenDataJar,
    TokenJar,
    husky_ast::jar::AstJar,
    EntityTreeJar,
    husky_toml_token::jar::TomlTokenJar,
    TomlAstJar,
    ManifestAstJar,
    CorgiConfigJar,
    CorgiConfigAstJar,
    ManifestJar,
    SynExprJar,
    SynDefnJar,
    SynDeclJar,
    TermPreludeJar,
    husky_dec_term::jar::DecTermJar,
    DecSignatureJar,
    husky_dec_ty::jar::DecTypeJar,
    EthTermJar,
    EthSignatureJar,
    FlyTermJar,
    SemExprJar,
    husky_sem_place_contract::jar::SemPlaceContractJar,
    husky_sem_item_path_deps::jar::SemItemPathDepsJar,
    husky_sem_static_mut_deps::jar::SemStaticMutDepsJar,
    husky_sem_var_deps::jar::SemVarDepsJar,
    husky_hir_ty::jar::HirTypeJar,
    husky_hir_eager_expr::jar::HirEagerExprJar,
    husky_hir_lazy_expr::jar::HirLazyExprJar,
    husky_hir_expr::jar::HirExprJar,
    husky_hir_prelude::jar::HirPreludeJar,
    HirDeclJar
)]
pub(crate) struct DB;

fn module_hir_decls(db: &::salsa::Db, module_path: ModulePath) -> Vec<HirDecl> {
    module_item_paths(db, module_path)
        .iter()
        .filter_map(|path| path.hir_decl(db))
        .collect()
}

#[test]
fn module_hir_decls_works() {
    DB::ast_rich_test_debug_with_db(
        module_hir_decls,
        &AstTestConfig::new(
            "module_hir_decls",
            FileExtensionConfig::Markdown,
            TestDomainsConfig::HIR,
        ),
    );
}
