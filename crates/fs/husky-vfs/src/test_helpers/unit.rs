use lock::ExpectUnitPath;

use super::*;
use crate::jar::VfsDb;

pub(crate) fn collect_units_from_package_path<M, U: IsVfsTestUnit<M>>(
    db: &::salsa::Db,
    package_path: PackagePath,
) -> Vec<U> {
    let units = U::collect_from_package_path_aux(db, package_path).collect::<Vec<_>>();
    for i in 0..units.len() {
        for j in (i + 1)..units.len() {
            assert_ne!(units[i], units[j])
        }
    }
    units
}

pub trait IsVfsTestUnit<M>: Copy + std::fmt::Debug + salsa::DebugWithDb + Eq {
    fn collect_from_package_path_aux(
        db: &::salsa::Db,
        package_path: PackagePath,
    ) -> impl Iterator<Item = Self>;
    fn determine_expect_unit_path(
        self,
        db: &::salsa::Db,
        package_expect_files_dir: &Path,
        config: &VfsTestConfig,
    ) -> ExpectUnitPath;

    fn determine_adversarial_path(
        self,
        db: &::salsa::Db,
        adversarial_kind: AdversarialKind,
        package_adversarials_dir: &Path,
        config: &VfsTestConfig,
    ) -> Option<PathBuf>;
    #[deprecated(note = "use downcast instead")]
    fn vfs_test_unit_downcast_as_module_path(self) -> Option<ModulePath>;
}

impl IsVfsTestUnit<Jar> for PackagePath {
    fn collect_from_package_path_aux(
        _db: &::salsa::Db,
        package_path: PackagePath,
    ) -> impl Iterator<Item = Self> {
        [package_path].into_iter()
    }

    fn determine_adversarial_path(
        self,
        _db: &::salsa::Db,
        _adversarial_kind: AdversarialKind,
        _package_adversarials_dir: &Path,
        _config: &VfsTestConfig,
    ) -> Option<PathBuf> {
        None
    }

    fn vfs_test_unit_downcast_as_module_path(self) -> Option<ModulePath> {
        None
    }

    fn determine_expect_unit_path(
        self,
        db: &salsa::Db,
        package_expect_files_dir: &Path,
        config: &VfsTestConfig,
    ) -> ExpectUnitPath {
        ExpectUnitPath::Single(
            package_expect_files_dir
                .join(config.test_name())
                .with_extension(config.expect_file_extension().str()),
        )
    }
}

impl IsVfsTestUnit<Jar> for CratePath {
    fn collect_from_package_path_aux(
        db: &::salsa::Db,
        package_path: PackagePath,
    ) -> impl Iterator<Item = Self> {
        package_path
            .crate_paths(db)
            .expect("no vfs error in testing")
            .iter()
            .copied()
    }

    fn determine_adversarial_path(
        self,
        _db: &::salsa::Db,
        _adversarial_kind: AdversarialKind,
        _package_adversarials_dir: &Path,
        _config: &VfsTestConfig,
    ) -> Option<PathBuf> {
        None
    }

    fn vfs_test_unit_downcast_as_module_path(self) -> Option<ModulePath> {
        None
    }

    fn determine_expect_unit_path(
        self,
        db: &salsa::Db,
        package_expect_files_dir: &Path,
        config: &VfsTestConfig,
    ) -> ExpectUnitPath {
        ExpectUnitPath::Single(package_expect_files_dir.join(format!(
            "{}/{}.{}",
            config.test_name(),
            match self.kind(db) {
                CrateKind::Lib => format!("src/lib"),
                CrateKind::Main => format!("src/main"),
                CrateKind::Task => format!("task"),
                CrateKind::Requirements => format!("requirements"),
                CrateKind::Bin(_) => todo!(),
                CrateKind::IntegratedTest(_) => todo!(),
                CrateKind::Example => todo!(),
            },
            config.expect_file_extension().str()
        )))
    }
}

impl IsVfsTestUnit<Jar> for ModulePath {
    fn collect_from_package_path_aux(
        db: &::salsa::Db,
        package_path: PackagePath,
    ) -> impl Iterator<Item = Self> {
        db.collect_probable_modules(package_path).into_iter()
    }

    fn determine_adversarial_path(
        self,
        db: &::salsa::Db,
        adversarial_kind: AdversarialKind,
        package_adversarials_dir: &Path,
        config: &VfsTestConfig,
    ) -> Option<PathBuf> {
        Some(
            self.relative_stem(db)
                .to_logical_path(package_adversarials_dir.join(config.test_name()))
                .with_extension(&format!(
                    "{}.{}",
                    adversarial_kind.as_str(),
                    config.adversarial_extension()
                )),
        )
    }

    fn vfs_test_unit_downcast_as_module_path(self) -> Option<ModulePath> {
        Some(self)
    }

    fn determine_expect_unit_path(
        self,
        db: &salsa::Db,
        package_expect_files_dir: &Path,
        config: &VfsTestConfig,
    ) -> ExpectUnitPath {
        ExpectUnitPath::Single(
            self.relative_stem(db)
                .to_logical_path(package_expect_files_dir)
                .with_extension(config.test_name())
                .with_added_extension(config.expect_file_extension().str()),
        )
    }
}
