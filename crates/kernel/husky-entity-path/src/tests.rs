use crate::*;
use husky_coword::jar::CowordJar;
use salsa::DebugWithDb;

#[salsa::db(CowordJar, husky_vfs::jar::VfsJar, Jar)]
#[derive(Default)]
pub(crate) struct DB;

#[test]
fn item_path_debug_works() {
    use husky_vfs::test_helpers::jar::VfsTestUtilsDb;

    let db = DB::default();
    let db = &*db;
    let toolchain = db.dev_toolchain().unwrap();
    let item_path_menu = item_path_menu(db, toolchain);
    expect_test::expect![[r#"
        TypePath(`core::num::i32`, `Extern`)
    "#]]
    .assert_debug_eq(&item_path_menu.i32_ty_path().debug(db));
}
