pub(crate) use husky_vfs::test_helpers::*;

use crate::*;
use husky_coword::jar::CowordJar;

#[salsa::db(
    CowordJar,
    husky_vfs::jar::VfsJar,
    husky_toml_token::jar::TomlTokenJar,
    TomlAstJar
)]
struct DB;

#[test]
fn manifest_ast_works() {
    DB::vfs_rich_test_debug_with_db(
        |db, path| db.package_manifest_toml_ast_sheet(path),
        &VfsTestConfig::new(
            "package_manifest_ast_sheet_sheet",
            FileExtensionConfig::Markdown,
            TestDomainsConfig::TOML,
        ),
    );
}
