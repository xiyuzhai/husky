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
    husky_sem_expr::jar::SemExprJar,
    Jar
)]
#[derive(Default)]
pub(crate) struct DB;
