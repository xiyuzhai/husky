pub(crate) use crate::test_helpers::*;

use crate::*;
use husky_coword::jar::CowordJar;
use husky_term_prelude::jar::TermPreludeJar;
use husky_token::TokenJar;
use husky_vfs::path::module_path::ModulePath;

#[salsa::db(
    CowordJar,
    husky_vfs::jar::VfsJar,
    husky_entity_path::jar::EntityPathJar,
    husky_token_data::jar::TokenDataJar,
    husky_text::jar::TextJar,
    TokenJar,
    crate::jar::AstJar,
    TermPreludeJar
)]
pub(crate) struct DB;

#[test]
fn ast_sheet_works() {
    DB::token_rich_test_debug_with_db(
        |db, module_path: ModulePath| module_path.ast_sheet(db),
        &TokenTestConfig::new(
            "ast_sheet",
            FileExtensionConfig::Markdown,
            TestDomainsConfig::SYNTAX,
        ),
    );
}
