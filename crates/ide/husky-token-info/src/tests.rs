pub(crate) use husky_ast::test_helpers::*;

use crate::*;
use husky_corgi_config::jar::CorgiConfigJar;
use husky_corgi_config_ast::CorgiConfigAstJar;
use husky_coword::jar::CowordJar;
use husky_dec_signature::jar::DecSignatureJar;
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
use husky_toml_ast::TomlAstJar;

#[salsa::db(
    husky_vfs::jar::VfsJar,
    CowordJar,
    husky_token_data::jar::TokenDataJar,
    husky_text::jar::TextJar,
    TokenJar,
    husky_entity_path::jar::EntityPathJar,
    husky_toml_token::jar::TomlTokenJar,
    TomlAstJar,
    ManifestAstJar,
    CorgiConfigJar,
    CorgiConfigAstJar,
    ManifestJar,
    husky_ast::jar::AstJar,
    husky_entity_tree::jar::EntityTreeJar,
    SynDeclJar,
    SynDefnJar,
    SynExprJar,
    husky_place::jar::PlaceJar,
    TermPreludeJar,
    husky_dec_term::jar::DecTermJar,
    DecSignatureJar,
    husky_dec_ty::jar::DecTypeJar,
    EthTermJar,
    EthSignatureJar,
    FlyTermJar,
    SemExprJar,
    husky_sem_place_contract::jar::SemPlaceContractJar,
    TokenInfoJar
)]
#[derive(Default)]
pub(crate) struct DB;

#[test]
fn token_infer_sheet_works() {
    DB::ast_rich_test_debug_with_db(
        TokenInfoDb::token_info_sheet,
        &AstTestConfig::new(
            "token_infer_sheet",
            FileExtensionConfig::Markdown,
            TestDomainsConfig::IDE,
        ),
    )
}
