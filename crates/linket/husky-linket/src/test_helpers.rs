use super::*;
use husky_entity_path::path::major_item::{connection::MajorItemConnection, form::MajorFormPath};
use husky_entity_tree::helpers::paths::module_test_paths;
use husky_hir_decl::decl::HasHirDecl;
use husky_vfs::{jar::VfsDb, test_helpers::*};
use rich_test::lock::ExpectUnitPath;

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TestLinket {
    path: MajorFormPath,
    linket: Linket,
}

impl std::ops::Deref for TestLinket {
    type Target = Linket;

    fn deref(&self) -> &Self::Target {
        &self.linket
    }
}

impl TestLinket {
    pub fn path(self, db: &salsa::Db) -> MajorFormPath {
        self.path
    }

    pub fn linket(self, db: &::salsa::Db) -> Linket {
        self.linket
    }
}

impl IsVfsTestUnit<Jar> for TestLinket {
    fn collect_from_package_path_aux(
        db: &salsa::Db,
        package_path: husky_vfs::path::package_path::PackagePath,
    ) -> impl Iterator<Item = Self> {
        db.collect_probable_modules(package_path)
            .into_iter()
            .flat_map(|module_path| module_test_paths(db, module_path).iter().copied())
            .map(|path| {
                assert!(path
                    .hir_decl(db)
                    .unwrap()
                    .template_parameters(db)
                    .unwrap()
                    .is_empty());
                TestLinket {
                    path,
                    linket: Linket::new(
                        db,
                        LinketData::MajorRitchie {
                            path,
                            instantiation: LinInstantiation::new_empty(path, false),
                        },
                    ),
                }
            })
    }

    fn determine_expect_unit_path(
        self,
        db: &salsa::Db,
        package_expect_files_dir: &std::path::Path,
        config: &VfsTestConfig,
    ) -> ExpectUnitPath {
        todo!()
        // let path = self.path;
        // let stem = path
        //     .module_path(db)
        //     .relative_stem(db)
        //     .to_logical_path(package_expect_files_dir);
        // match path.data(db).connection() {
        //     MajorItemConnection::Connected => stem.join(format!(
        //         "{}.{}",
        //         path.ident(db).data(db),
        //         config.expect_file_extension().str()
        //     )),
        //     MajorItemConnection::Disconnected(_) => todo!(),
        // }
    }

    fn determine_adversarial_path(
        self,
        db: &salsa::Db,
        adversarial_kind: AdversarialKind,
        package_adversarials_dir: &std::path::Path,
        config: &VfsTestConfig,
    ) -> Option<std::path::PathBuf> {
        None
    }

    fn vfs_test_unit_downcast_as_module_path(
        self,
    ) -> Option<husky_vfs::path::module_path::ModulePath> {
        todo!()
    }
}
