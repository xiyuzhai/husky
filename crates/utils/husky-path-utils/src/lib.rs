pub mod dev_paths;
mod error;
mod module_tree;
pub mod rel;
pub mod rust;
#[cfg(test)]
mod tests;

pub use self::dev_paths::*;
pub use self::error::*;
pub use self::rel::*;
use husky_minimal_toml_utils::read_package_name_string_from_manifest;
pub use module_tree::*;

pub use std::path::{Path, PathBuf};

#[cfg(test)]
use self::tests::*;
use husky_check_utils::should_satisfy;

use relative_path::{RelativePath, RelativePathBuf};

pub fn path_has_file_name(path: &Path, name: &str) -> bool {
    path.file_name().map(|s| s.to_string_lossy()) == Some(name.into())
}

pub fn path_file_name_str(path: &Path) -> Option<String> {
    path.file_name().map(|s| s.to_string_lossy().to_string())
}

pub fn path_parent_file_name_str(path: &Path) -> Option<String> {
    if let Some(parent) = path.parent() {
        parent.file_name().map(|s| s.to_string_lossy().to_string())
    } else {
        None
    }
}

pub fn path_has_extension(path: &Path, extension: &str) -> bool {
    path.extension().map(|s| s.to_string_lossy()) == Some(extension.into())
}

/// find every paths
pub fn find_paths(dir: &Path) -> Vec<PathBuf> {
    let mut paths: Vec<PathBuf> = vec![];
    find_paths_aux(dir, &mut paths, &|_path| true);
    paths
}

/// find every dirs
pub fn find_dirs(dir: &Path) -> Vec<PathBuf> {
    let mut paths: Vec<PathBuf> = vec![];
    find_paths_aux(dir, &mut paths, &|path| path.exists() && path.is_dir());
    paths
}

/// find every dirs with name
pub fn find_dirs_ending_with(dir: &Path, child: impl AsRef<Path>) -> Vec<PathBuf> {
    let mut paths: Vec<PathBuf> = vec![];
    let child = child.as_ref();
    find_paths_aux(dir, &mut paths, &|path| {
        path.exists() && path.is_dir() && path.ends_with(child)
    });
    paths
}

pub fn find_regular_files(dir: &Path) -> Vec<PathBuf> {
    let mut paths: Vec<PathBuf> = vec![];
    find_paths_aux(dir, &mut paths, &|path| path.exists() && path.is_file());
    paths
}

pub fn find_paths_aux(dir: &Path, paths: &mut Vec<PathBuf>, predicate: &impl Fn(&Path) -> bool) {
    if let Ok(read_dir) = std::fs::read_dir(dir) {
        for entry in read_dir {
            if let Ok(entry) = entry {
                let path = entry.path();
                if path.is_dir() && path.exists() {
                    find_paths_aux(&path, paths, predicate)
                }
                if predicate(&path) {
                    paths.push(path)
                }
            }
        }
    }
}

pub fn collect_package_dirs_deprecated(dir: &Path) -> Vec<PathBuf> {
    should_satisfy!(dir, |dir: &Path| dir.is_dir());
    let main_path = dir.join("main.hsy");
    if main_path.exists() {
        return vec![dir.to_path_buf()];
    } else {
        let mut pack_paths = vec![];
        for entry in std::fs::read_dir(dir).unwrap() {
            let entry = entry.unwrap();
            let subpath = entry.path();
            if subpath.is_dir() {
                pack_paths.extend(collect_package_dirs_deprecated(&subpath))
            }
        }
        pack_paths
    }
}

pub fn collect_husky_package_dirs(db: &::salsa::Db, dir: &Path) -> Vec<PathBuf> {
    should_satisfy!(&dir, |dir: &Path| dir.is_dir());
    let mut pack_paths = vec![];
    collect_husky_package_dirs_aux(db, dir, &mut pack_paths);
    pack_paths.sort();
    pack_paths
}

fn collect_husky_package_dirs_aux(db: &::salsa::Db, dir: &Path, pack_paths: &mut Vec<PathBuf>) {
    let manifest_path = dir.join("Corgi.toml");
    for entry in std::fs::read_dir(&dir).unwrap() {
        let entry = entry.unwrap();
        let subpath = entry.path();
        if subpath.is_dir() {
            collect_husky_package_dirs_aux(db, &subpath, pack_paths)
        }
    }
    if let Some(_name) = read_package_name_string_from_manifest(&manifest_path) {
        pack_paths.push(dir.to_owned())
    }
}

pub fn collect_package_relative_dirs(base: &Path) -> Vec<RelativePathBuf> {
    should_satisfy!(&base, |dir: &Path| dir.is_dir());
    let mut pack_paths = vec![];
    let dir = RelativePathBuf::from(".");
    collect_package_relative_dirs_aux(base, &dir, &mut pack_paths);
    pack_paths.sort();
    pack_paths
}

fn collect_package_relative_dirs_aux(
    base: &Path,
    dir: &RelativePath,
    pack_paths: &mut Vec<RelativePathBuf>,
) {
    let manifest_path = dir.join("Corgi.toml");
    for entry in std::fs::read_dir(&dir.to_logical_path(base)).unwrap() {
        let entry = entry.unwrap();
        let subpath = entry.path();
        if subpath.is_dir() {
            collect_package_relative_dirs_aux(
                base,
                &dir.join(subpath.file_name().unwrap().to_str().unwrap()),
                pack_paths,
            )
        }
    }
    if let Some(_name) =
        read_package_name_string_from_manifest(&manifest_path.to_logical_path(base))
    {
        pack_paths.push(dir.to_owned())
    }
}

#[test]
fn collect_package_relative_dirs_works() {
    use salsa::DebugWithDb;
    let db = DB::default();
    let db = &*db;
    let cargo_manifest_dir: PathBuf = std::env::var("CARGO_MANIFEST_DIR").unwrap().into();
    let library_dir = cargo_manifest_dir
        .join("../../../library")
        .canonicalize()
        .unwrap();
    expect_test::expect![[r#"
        [
            "./core",
            "./std",
        ]
    "#]]
    .assert_debug_eq(&collect_package_relative_dirs(&library_dir).debug(db));

    let examples_dir = cargo_manifest_dir
        .join("../../../examples")
        .canonicalize()
        .unwrap();
    expect_test::expect![[r#"
        [
            "./algorithms/quick-sort",
            "./basics/semantics-basics",
            "./basics/syntax-basics",
            "./cybertron-mini-lean-compiler",
            "./mnist-classifier",
        ]
    "#]]
    .assert_debug_eq(&collect_package_relative_dirs(&examples_dir).debug(db));
}

#[test]
fn collect_package_dirs_works() {
    let db = DB::default();
    let db = &*db;
    fn t(db: &::salsa::Db, dir: &Path) {
        assert_eq!(
            collect_package_relative_dirs(dir)
                .into_iter()
                .map(|rpath| rpath.to_logical_path(dir))
                .collect::<Vec<_>>(),
            collect_husky_package_dirs(db, dir)
        )
    }
    let cargo_manifest_dir: PathBuf = std::env::var("CARGO_MANIFEST_DIR").unwrap().into();
    t(
        &db,
        &cargo_manifest_dir
            .join("../../../library")
            .canonicalize()
            .unwrap(),
    );
    t(
        &db,
        &cargo_manifest_dir
            .join("../../../examples")
            .canonicalize()
            .unwrap(),
    )
}

pub fn collect_all_source_files(dir: PathBuf) -> Vec<PathBuf> {
    assert!(dir.is_dir());
    let mut source_files = vec![];
    for entry in std::fs::read_dir(dir).unwrap() {
        let entry = entry.unwrap();
        let subpath = entry.path();
        if subpath.is_dir() {
            source_files.extend(collect_all_source_files(subpath))
        } else {
            if subpath.extension().unwrap() == "hsy" {
                source_files.push(subpath)
            }
        }
    }
    source_files
}

#[inline(always)]
pub fn find_lang_dev_root() -> PathUtilsResult<PathBuf> {
    let cargo_manifest_dir: Option<PathBuf> = std::env::var("CARGO_MANIFEST_DIR")
        .ok()
        .map(|path| path.into());
    let current_dir = std::env::current_dir().expect("`current_dir` should be okay");
    let mut dir: &Path = if let Some(ref cargo_manifest_dir) = cargo_manifest_dir {
        cargo_manifest_dir
    } else {
        // this is handy for debugging in lldb
        println!("Warning: environment variable CARGO_MANIFEST_DIR not set!");
        println!("Use current dir {current_dir:?} as starting point for finding `lang_dev_root`");
        &current_dir
    };
    // search over ancestries
    loop {
        if dir.join("husky-toolchain.toml").exists() {
            assert!(dir.join("husky-toolchain.toml").is_file());
            assert!(dir.join(".corgi/config.toml").exists());
            assert!(dir.join(".corgi/config.toml").is_file());
            assert!(dir.join("library").exists());
            assert!(dir.join("library").is_dir());
            assert!(dir.join("examples").exists());
            assert!(dir.join("examples").is_dir());
            assert!(dir.join("registry").exists());
            assert!(dir.join("registry").is_dir());
            if cargo_manifest_dir.is_none() {
                println!("`lang_dev_root` is decided to be {dir:?}");
            }
            return Ok(dir.to_owned());
        }
        if let Some(new_library_parent_dir) = dir.parent() {
            dir = new_library_parent_dir
        } else {
            todo!()
        }
    }
}

#[inline(always)]
pub fn find_lang_dev_library_path() -> PathUtilsResult<PathBuf> {
    Ok(find_lang_dev_root()?.join("library"))
}

#[inline(always)]
pub fn derive_examples_dir_from_cargo_manifest_dir() -> PathUtilsResult<PathBuf> {
    Ok(find_lang_dev_root()?.join("examples"))
}

pub fn clear_directory(path: &Path) -> Result<(), std::io::Error> {
    // Get an iterator over the entries in the directory
    let entries = std::fs::read_dir(path)?;

    // Iterate over the entries and delete them
    for entry in entries {
        let entry = entry?;
        let entry_path = entry.path();
        if entry_path.is_dir() {
            // If the entry is a directory, clear it recursively
            clear_directory(&entry_path)?;
            std::fs::remove_dir(entry_path)?;
        } else {
            // If the entry is a file, delete it
            std::fs::remove_file(entry_path)?;
        }
    }

    Ok(())
}
