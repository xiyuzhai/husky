pub(crate) use husky_ast::test_helpers::*;

use crate::*;
use husky_corgi_config::jar::CorgiConfigJar;
use husky_corgi_config_ast::CorgiConfigAstJar;
use husky_coword::jar::CowordJar;
use husky_dec_signature::jar::DecSignatureJar;

use husky_entity_tree::jar::EntityTreeJar;
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
    husky_vfs::jar::VfsJar,
    husky_coword::jar::CowordJar,
    husky_text::jar::TextJar,
    husky_token_data::jar::TokenDataJar,
    husky_token::jar::TokenJar,
    husky_token_info::jar::TokenInfoJar,
    husky_entity_path::jar::EntityPathJar,
    husky_toml_token::jar::TomlTokenJar,
    husky_toml_ast::jar::TomlAstJar,
    husky_manifest_ast::jar::ManifestAstJar,
    husky_corgi_config::jar::CorgiConfigJar,
    husky_corgi_config_ast::jar::CorgiConfigAstJar,
    husky_manifest::jar::ManifestJar,
    husky_ast::jar::AstJar,
    husky_entity_tree::jar::EntityTreeJar,
    husky_syn_decl::jar::SynDeclJar,
    husky_syn_defn::jar::SynDefnJar,
    husky_syn_expr::jar::SynExprJar,
    husky_place::jar::PlaceJar,
    husky_term_prelude::jar::TermPreludeJar,
    husky_dec_term::jar::DecTermJar,
    husky_dec_signature::jar::DecSignatureJar,
    husky_dec_ty::jar::DecTypeJar,
    husky_eth_term::jar::EthTermJar,
    husky_eth_signature::jar::EthSignatureJar,
    husky_fly_term::jar::FlyTermJar,
    husky_sem_expr::jar::SemExprJar,
    husky_sem_place_contract::jar::SemPlaceContractJar,
    Jar
)]
#[derive(Default)]
pub(crate) struct DB;

#[test]
fn semantic_tokens_works() {
    DB::ast_rich_test_debug(
        |db, module_path| SemanticTokenDb::semantic_tokens_ext(db, module_path, None),
        &AstTestConfig::new(
            "semantic_tokens",
            FileExtensionConfig::Markdown,
            TestDomainsConfig::IDE,
        ),
    )
}
