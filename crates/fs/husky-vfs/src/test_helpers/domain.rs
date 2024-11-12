use super::*;

#[derive(Debug)]
#[salsa::derive_debug_with_db]
pub(super) struct TestDomain {
    src_base: PathBuf,
    expect_files_base: PathBuf,
    adversarials_base: Option<PathBuf>,
}

impl TestDomain {
    pub(super) fn new(
        src_base: PathBuf,
        expect_files_base: PathBuf,
        adversarials_base: Option<PathBuf>,
    ) -> Self {
        std::fs::create_dir_all(&expect_files_base).expect("failed_to_create_dir_all");
        adversarials_base.as_ref().map(|adversarials_base| {
            std::fs::create_dir_all(&adversarials_base).expect("failed_to_create_dir_all")
        });
        Self {
            src_base,
            expect_files_base,
            adversarials_base,
        }
    }

    pub(super) fn src_base(&self) -> &Path {
        &self.src_base
    }

    pub(super) fn expect_files_base(&self) -> &Path {
        &self.expect_files_base
    }

    pub(super) fn adversarials_base(&self) -> Option<&Path> {
        self.adversarials_base.as_ref().map(|p| p as &Path)
    }
}

pub struct TestDomainsConfig(TestDomainsConfigImpl);

pub enum TestDomainsConfigImpl {
    All,
    ExcludeLibraryAndAntiExamples,
    ExamplesOnly,
}

/// # exports
impl TestDomainsConfig {
    pub const COMPTIME: Self =
        TestDomainsConfig(TestDomainsConfigImpl::ExcludeLibraryAndAntiExamples);
    pub const DEVTIME: Self =
        TestDomainsConfig(TestDomainsConfigImpl::ExcludeLibraryAndAntiExamples);
    pub const FS: Self = TestDomainsConfig(TestDomainsConfigImpl::All);
    pub const HIR: Self = TestDomainsConfig(TestDomainsConfigImpl::All);
    pub const IDE: Self = TestDomainsConfig(TestDomainsConfigImpl::All);
    pub const LEX: Self = TestDomainsConfig(TestDomainsConfigImpl::All);
    pub const LINKET: Self =
        TestDomainsConfig(TestDomainsConfigImpl::ExcludeLibraryAndAntiExamples);
    pub const LINKTIME: Self =
        TestDomainsConfig(TestDomainsConfigImpl::ExcludeLibraryAndAntiExamples);
    pub const KERNEL: Self = TestDomainsConfig(TestDomainsConfigImpl::All);
    pub const SYNTAX: Self = TestDomainsConfig(TestDomainsConfigImpl::All);
    pub const SEMANTICS: Self = TestDomainsConfig(TestDomainsConfigImpl::All);
    pub const TOML: Self = TestDomainsConfig(TestDomainsConfigImpl::All);
    pub const VAL: Self = TestDomainsConfig(TestDomainsConfigImpl::ExcludeLibraryAndAntiExamples);
}

impl TestDomainsConfig {
    pub(super) fn test_domains(&self, cargo_manifest_dir: &Path) -> Vec<TestDomain> {
        let paths = HuskyLangDevPaths::new();
        match self.0 {
            TestDomainsConfigImpl::All => {
                vec![
                    TestDomain::new(
                        paths.library_dir().to_owned(),
                        cargo_manifest_dir.join("expect-files/library"),
                        None,
                    ),
                    TestDomain::new(
                        paths.examples_dir().to_owned(),
                        cargo_manifest_dir.join("expect-files/anti-examples"),
                        Some(cargo_manifest_dir.join("adversarials/anti-examples")),
                    ),
                    TestDomain::new(
                        paths.examples_dir().to_owned(),
                        cargo_manifest_dir.join("expect-files/examples"),
                        Some(cargo_manifest_dir.join("adversarials/examples")),
                    ),
                    TestDomain::new(
                        paths.registry_dir().to_owned(),
                        cargo_manifest_dir.join("expect-files/registry"),
                        Some(cargo_manifest_dir.join("adversarials/registry")),
                    ),
                ]
            }
            TestDomainsConfigImpl::ExcludeLibraryAndAntiExamples => {
                vec![
                    TestDomain::new(
                        paths.examples_dir().to_owned(),
                        cargo_manifest_dir.join("expect-files/examples"),
                        Some(cargo_manifest_dir.join("adversarials/examples")),
                    ),
                    TestDomain::new(
                        paths.registry_dir().to_owned(),
                        cargo_manifest_dir.join("expect-files/registry"),
                        Some(cargo_manifest_dir.join("adversarials/registry")),
                    ),
                ]
            }
            TestDomainsConfigImpl::ExamplesOnly => vec![TestDomain::new(
                paths.examples_dir().to_owned(),
                cargo_manifest_dir.join("expect-files/examples"),
                Some(cargo_manifest_dir.join("adversarials/examples")),
            )],
        }
    }
}
