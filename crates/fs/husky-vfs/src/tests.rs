use crate::{
    // watch::{WatchedVfs, DEBOUNCE_TEST_SLEEP_TIME},
    *,
};

#[salsa::db(Jar, husky_coword::jar::CowordJar)]
#[derive(Default)]
pub(crate) struct DB;

#[cfg(target_os = "linux")]
#[test]
fn watcher_works() {
    // let db = DB::default();
    // let tempdir = tempfile::tempdir().unwrap();
    // let some_pkg_dir = tempdir.path().join("somepath");
    // std::fs::create_dir(&some_pkg_dir).unwrap();
    // let path = some_pkg_dir.join("Corgi.toml");
    // let abs_path: VirtualPath = VirtualPath::try_new(&db, &path).unwrap();
    // let db = WatchedVfs::new(db);

    // std::fs::write(&path, "Hello, world!").expect("can't write");
    // assert!(db.query(|db| db
    //     .file_from_virtual_path(abs_path)
    //     .unwrap()
    //     .content(db.deref())
    //     == &FileContent::OnDisk("Hello, world!".to_owned())),);
    // std::fs::write(&path, "Hello, world!2").expect("can't write");
    // let _a = DEBOUNCE_TEST_SLEEP_TIME;
    // std::thread::sleep(DEBOUNCE_TEST_SLEEP_TIME);
    // assert!(db.query(|db| db
    //     .file_from_virtual_path(abs_path)
    //     .unwrap()
    //     .content(db.deref())
    //     == &FileContent::OnDisk("Hello, world!2".to_owned())))
}
