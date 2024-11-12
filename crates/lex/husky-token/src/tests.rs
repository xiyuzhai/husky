mod adv;

pub(crate) use husky_vfs::test_helpers::*;

use crate::*;
use husky_coword::jar::CowordJar;
use husky_expect_test_snippets_utils::*;
use husky_vfs::{script::Script, *};
use salsa::DebugWithDb;

#[salsa::db(
    CowordJar,
    husky_vfs::jar::VfsJar,
    husky_token_data::jar::TokenDataJar,
    TokenJar,
    husky_term_prelude::jar::TermPreludeJar,
    husky_entity_path::jar::EntityPathJar
)]
#[derive(Default)]
pub(crate) struct DB;

fn tokenize_snippet_debug(snippet: &str) -> String {
    let db = DB::default();
    let db = &*db;
    let snippet = Script::new_dev_snippet(snippet, db);
    format!("{:#?}", db.chunk_token_sheet_data(snippet).debug(db))
}

#[test]
fn tokenize_works() {
    expect_test_snippets("snippets", &tokenize_snippet_debug);
}

#[test]
fn token_sheet_works() {
    DB::vfs_rich_test_debug_with_db(
        |db, module_path| db.token_sheet_data(module_path),
        &VfsTestConfig::new(
            "token_sheet",
            FileExtensionConfig::Markdown,
            TestDomainsConfig::KERNEL,
        ),
    )
}
