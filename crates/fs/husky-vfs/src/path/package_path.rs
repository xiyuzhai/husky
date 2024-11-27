use super::*;
use husky_coword::Ident;
use husky_minimal_toml_utils::read_package_name_kebab_from_manifest;
use std::path::Path;
use url::Url;

/// deprecated
#[test]
fn package_ident_works() {
    let db = DB::default();
    let db = &*db;
    let _toolchain = db.dev_toolchain().unwrap();
    let coword_menu = coword_menu(db);
    let path_menu = db.dev_path_menu().unwrap();
    assert_eq!(path_menu.core_package().ident(db), coword_menu.core_ident());
    assert_eq!(path_menu.std_package().ident(db), coword_menu.std_ident());
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
#[salsa::derive_debug_with_db]
pub enum PackagePathSource {
    Library,
    Registry {
        registry_path: RegistryPath,
        version: semver::Version,
    },
    Local {
        path: VirtualPath,
    },
    Git {
        url: Url,
    },
}

#[salsa::interned(constructor = new_inner)]
pub struct PackagePath {
    pub toolchain: Toolchain,
    pub name: Kebab,
    #[return_ref]
    pub data: PackagePathSource,
}

impl PackagePath {
    /// if name is `core` or `std` make sure that the package is the toolchain one
    pub fn new_local_or_toolchain_package(
        db: &::salsa::Db,
        toolchain: Toolchain,
        path: &Path,
    ) -> VfsResult<Self> {
        let manifest_path = path.join("Corgi.toml");
        let name = read_package_name_kebab_from_manifest(db, &manifest_path)??;
        match name.data(db) {
            "core" | "std" => {
                debug_assert_eq!(
                    std::fs::canonicalize(path.parent().unwrap()).unwrap(),
                    std::fs::canonicalize(toolchain.library_path(db)).unwrap()
                );
                Ok(Self::new_toolchain_package(db, toolchain, name))
            }
            _ => Ok(PackagePath::new_inner(
                db,
                toolchain,
                name,
                PackagePathSource::Local {
                    path: VirtualPath::try_new(db, path)?,
                },
            )),
        }
    }

    pub fn new_toolchain_package(db: &::salsa::Db, toolchain: Toolchain, name: Kebab) -> Self {
        PackagePath::new_inner(db, toolchain, name, PackagePathSource::Library)
    }

    pub fn new_registry_package(
        db: &::salsa::Db,
        toolchain: Toolchain,
        name: Kebab,
        registry_path: RegistryPath,
        version: semver::Version,
    ) -> Self {
        PackagePath::new_inner(
            db,
            toolchain,
            name,
            PackagePathSource::Registry {
                registry_path,
                version,
            },
        )
    }

    pub fn ident(self, db: &::salsa::Db) -> Ident {
        self.name(db).ident(db)
    }

    pub fn name_str<'a>(self, db: &'a ::salsa::Db) -> &'a str {
        self.name(db).data(db)
    }

    pub fn name_string(self, db: &::salsa::Db) -> String {
        self.name(db).data(db).to_string()
    }

    pub fn dir(self, db: &::salsa::Db) -> VfsResult<VirtualPath> {
        package_dir(db, self)
    }

    pub fn manifest_path(self, db: &::salsa::Db) -> VfsResult<ManifestPath> {
        package_manifest_path(db, self)
    }

    pub fn task_crate_path(self, db: &::salsa::Db) -> VfsMaybeResult<CratePath> {
        package_task_crate_path(db, self)
    }

    pub fn task_module_path(self, db: &::salsa::Db) -> VfsResult<Option<ModulePath>> {
        todo!()
    }

    pub fn is_virtual(self, db: &::salsa::Db) -> bool {
        is_package_path_virtual(db, self)
    }
}

#[salsa::tracked(jar = VfsJar)]
fn is_package_path_virtual(db: &::salsa::Db, package_path: PackagePath) -> bool {
    let dir = package_path.dir(db).expect("what to do");
    let cargo_toml_path = dir.join("Cargo.toml", db);
    match cargo_toml_path.exists(db) {
        Ok(exists) => exists,
        Err(_) => todo!(),
    }
}

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RegistryPath(VirtualPath);

impl RegistryPath {
    pub fn new(path: VirtualPath) -> Self {
        Self(path)
    }

    pub fn path(self) -> VirtualPath {
        self.0
    }
}

#[salsa::tracked(jar = VfsJar)]
pub(crate) fn package_dir(db: &::salsa::Db, package: PackagePath) -> VfsResult<VirtualPath> {
    match package.data(db) {
        PackagePathSource::Library => VirtualPath::try_new(
            db,
            &package
                .toolchain(db)
                .library_path(db)
                .join(package.name(db).data(db)),
        ),
        PackagePathSource::Registry {
            registry_path,
            version,
            ..
        } => VirtualPath::try_new(
            db,
            registry_path.path().data(db).join(format!(
                "{}-{}.{}.{}",
                package.name(db).data(db),
                version.major,
                version.minor,
                version.patch
            )),
        ),
        PackagePathSource::Local { path } => Ok(path.clone()),
        PackagePathSource::Git { .. } => todo!(),
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ManifestPath(VirtualPath);

impl ManifestPath {
    pub fn path(self) -> VirtualPath {
        self.0
    }
}

#[salsa::tracked(jar = VfsJar)]
pub(crate) fn package_manifest_path(
    db: &::salsa::Db,
    package: PackagePath,
) -> VfsResult<ManifestPath> {
    Ok(ManifestPath(VirtualPath::try_new(
        db,
        package.dir(db)?.data(db).join("Corgi.toml"),
    )?))
}

#[salsa::tracked]
fn package_task_crate_path(db: &::salsa::Db, package: PackagePath) -> VfsMaybeResult<CratePath> {
    CratePath::new(package, CrateKind::Task, db)
}
