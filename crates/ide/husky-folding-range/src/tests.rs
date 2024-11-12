pub(crate) use husky_ast::test_helpers::*;

use crate::*;
use husky_coword::jar::CowordJar;
use husky_token::TokenJar;

#[salsa::db(
    CowordJar,
    husky_corgi_config::jar::CorgiConfigJar,
    husky_vfs::jar::VfsJar,
    husky_entity_path::jar::EntityPathJar,
    husky_term_prelude::jar::TermPreludeJar,
    husky_token_data::jar::TokenDataJar,
    husky_text::jar::TextJar,
    TokenJar,
    husky_ast::jar::AstJar,
    Jar,
    husky_toml_token::jar::TomlTokenJar,
    husky_toml_ast::jar::TomlAstJar,
    husky_corgi_config_ast::jar::CorgiConfigAstJar
)]
#[derive(Default)]
pub struct DB;

#[test]
fn folding_ranges_works() {
    DB::ast_rich_test_debug(
        |db, module_path| db.folding_ranges(module_path),
        &AstTestConfig::new(
            "folding_ranges",
            FileExtensionConfig::Markdown,
            TestDomainsConfig::IDE,
        ),
    );
}
