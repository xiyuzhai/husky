//! this is about the rust packages, not the husky packages
use crate::{
    defn::module_defn_rust_transpilation,
    linket::package_linkets_transpilation,
    manifest::{linkets_package_manifest, source_package_manifest},
    *,
};
use ::relative_path::RelativePathBuf;
use husky_corgi_config::transpilation_setup::TranspilationSetup;
use husky_entity_tree::helpers::paths::crate_module_paths;
use husky_io_utils::error::IoResult;
use husky_manifest::HasManifest;
use husky_vfs::{
    path::{
        crate_path::CrateKind,
        linktime_target_path::{LinktimeTargetPath, LinktimeTargetPathData},
        module_path::ModulePathData,
    },
    *,
};
use pathdiff::diff_paths;
use std::path::Path;

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct RustTranspilationPackage {
    pub(crate) target_path: LinktimeTargetPath,
    pub(crate) data: RustTranspilationPackageData,
}

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RustTranspilationPackageData {
    Source { package_path: PackagePath },
    Linkets,
}

impl RustTranspilationPackage {
    pub(crate) fn name(self, db: &::salsa::Db) -> String {
        match self.data {
            RustTranspilationPackageData::Source { package_path } => {
                match package_path.name(db).data(db) {
                    "core" => "husky-core".to_string(),
                    name => name.to_string(),
                }
            }
            RustTranspilationPackageData::Linkets => {
                format!("{}-linkets", self.target_path.name(db).data(db))
            }
        }
    }

    pub(crate) fn path_in_workspace(
        self,
        rust_workspace_abs_dir: &Path,
        db: &::salsa::Db,
    ) -> String {
        match self.data {
            RustTranspilationPackageData::Source { package_path } => {
                if package_path.is_virtual(db) {
                    diff_paths(
                        package_path.dir(db).unwrap().abs_path(db).unwrap(),
                        rust_workspace_abs_dir,
                    )
                    .unwrap()
                    .as_os_str()
                    .to_str()
                    .unwrap()
                    .to_string()
                } else {
                    self.name(db)
                }
            }
            RustTranspilationPackageData::Linkets => self.name(db),
        }
    }

    pub(crate) fn is_virtual_source(self, db: &::salsa::Db) -> bool {
        match self.data {
            RustTranspilationPackageData::Source { package_path } => package_path.is_virtual(db),
            RustTranspilationPackageData::Linkets => false,
        }
    }
}

#[salsa::tracked(return_ref)]
pub(crate) fn rust_transpilation_packages(
    db: &::salsa::Db,
    target_path: LinktimeTargetPath,
) -> Vec<RustTranspilationPackage> {
    let mut packages = vec![];
    packages.extend(
        target_path
            .full_dependencies(db)
            .expect("no error at this stage")
            .iter()
            .flat_map(|&dep_package_path| {
                [RustTranspilationPackage {
                    target_path,
                    data: RustTranspilationPackageData::Source {
                        package_path: dep_package_path,
                    },
                }]
            }),
    );
    packages.push(RustTranspilationPackage {
        target_path,
        data: RustTranspilationPackageData::Linkets,
    });
    packages
}

#[test]
fn rust_transpilation_packages_works() {
    DB::ast_rich_test_debug_with_db(
        |db, package_path: PackagePath| {
            let linktime_target_path = LinktimeTargetPath::new_package(package_path, db);
            rust_transpilation_packages(db, linktime_target_path)
        },
        &AstTestConfig::new(
            "rust_transpilation_packages",
            FileExtensionConfig::Markdown,
            TestDomainsConfig::COMPTIME,
        ),
    )
}

impl RustTranspilationPackage {
    pub(crate) fn transpile_to_fs(
        &self,
        setup: TranspilationSetup,
        db: &::salsa::Db,
    ) -> IoResult<()> {
        let workspace_dir = self.target_path.rust_workspace_abs_dir(db);
        match self.data {
            package::RustTranspilationPackageData::Source { package_path } => {
                transpile_source_package_to_fs(setup, workspace_dir, package_path, db)
            }
            package::RustTranspilationPackageData::Linkets => {
                transpile_linkets_package_to_fs(setup, workspace_dir, self.target_path, db)
            }
        }
    }
}

fn transpile_source_package_to_fs(
    setup: TranspilationSetup,
    rust_workspace_dir: &std::path::Path,
    package_path: PackagePath,
    db: &::salsa::Db,
) -> IoResult<()> {
    if package_path.is_virtual(db) {
        return Ok(());
    }
    let package_dir = rust_workspace_dir.join(package_path.name(db).data(db));
    let cargo_toml_path = package_dir.join("Cargo.toml");
    husky_io_utils::diff_write(
        &cargo_toml_path,
        source_package_manifest(db, package_path, setup),
        true,
    );
    for &crate_path in package_path
        .crate_paths(db)
        .expect("no vfs error at this stage")
    {
        match crate_path.kind(db) {
            CrateKind::Lib | CrateKind::Main => {
                for &module_path in crate_module_paths(db, crate_path) {
                    husky_io_utils::diff_write(
                        &module_relative_path_for_transpilation(db, module_path)
                            .to_path(&package_dir),
                        module_defn_rust_transpilation(db, module_path, setup),
                        true,
                    );
                }
            }
            CrateKind::Requirements | CrateKind::Task => (),
            CrateKind::Bin(_) => todo!(),
            CrateKind::IntegratedTest(_) => todo!(),
            CrateKind::Example => todo!(),
        }
    }
    Ok(())
}

#[salsa::tracked(return_ref)]
fn module_relative_path_for_transpilation(
    db: &::salsa::Db,
    module_path: ModulePath,
) -> RelativePathBuf {
    match module_path.data(db) {
        ModulePathData::Root(crate_path) => match crate_path.kind(db) {
            CrateKind::Lib | CrateKind::Main => RelativePathBuf::from_path("src/lib.rs").unwrap(),
            CrateKind::Requirements | CrateKind::Task => todo!(),
            CrateKind::Bin(_) => todo!(),
            CrateKind::IntegratedTest(_) => todo!(),
            CrateKind::Example => todo!(),
        },
        ModulePathData::Child { .. } => module_path
            .relative_dir_for_submodules(db)
            .with_extension("rs"),
        ModulePathData::Script { .. } => unreachable!(),
    }
}

fn transpile_linkets_package_to_fs(
    setup: TranspilationSetup,
    rust_workspace_dir: &std::path::Path,
    target_path: LinktimeTargetPath,
    db: &::salsa::Db,
) -> IoResult<()> {
    let package_dir = rust_workspace_dir.join(format!("{}-linkets", target_path.name(db).data(db)));
    let src_dir = package_dir.join("src");
    let cargo_toml_path = package_dir.join("Cargo.toml");
    husky_io_utils::diff_write(
        &cargo_toml_path,
        linkets_package_manifest(db, target_path, setup),
        true,
    );
    husky_io_utils::diff_write(
        &src_dir.join("lib.rs"),
        package_linkets_transpilation(db, target_path, setup),
        true,
    );
    Ok(())
}
