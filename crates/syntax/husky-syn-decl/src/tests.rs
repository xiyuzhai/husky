pub(crate) use husky_ast::test_helpers::*;
pub(crate) use husky_entity_path::menu::item_path_menu;

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
    husky_entity_tree::jar::EntityTreeJar,
    husky_toml_token::jar::TomlTokenJar,
    TomlAstJar,
    ManifestAstJar,
    CorgiConfigJar,
    CorgiConfigAstJar,
    ManifestJar,
    husky_syn_expr::jar::SynExprJar,
    SynDeclJar
)]
#[derive(Default)]
pub(crate) struct DB;

#[test]
fn menu_item_decl_works() {
    let db = DB::default();
    let db = &*db;
    let toolchain = db.dev_toolchain().unwrap();
    let item_path_menu = item_path_menu(db, toolchain);
    let i32_ty_path_decl = item_path_menu.i32_ty_path().syn_decl(db).unwrap();
    salsa::assert_eq_with_db!(db, i32_ty_path_decl.template_parameters(db).len(), 0);
}
