pub(crate) use husky_ast::test_helpers::*;

use crate::*;
use husky_corgi_config::jar::CorgiConfigJar;
use husky_corgi_config_ast::CorgiConfigAstJar;
use husky_coword::jar::CowordJar;
use husky_manifest::jar::ManifestJar;
use husky_manifest_ast::jar::ManifestAstJar;
use husky_term_prelude::jar::TermPreludeJar;
use husky_token::TokenJar;
use husky_toml_ast::TomlAstJar;

#[salsa::db(
    CowordJar,
    husky_vfs::jar::VfsJar,
    husky_entity_path::jar::EntityPathJar,
    TermPreludeJar,
    husky_token_data::jar::TokenDataJar,
    husky_text::jar::TextJar,
    TokenJar,
    husky_ast::jar::AstJar,
    Jar,
    husky_toml_token::jar::TomlTokenJar,
    TomlAstJar,
    ManifestAstJar,
    CorgiConfigJar,
    CorgiConfigAstJar,
    ManifestJar
)]
#[derive(Default)]
pub(crate) struct DB;
