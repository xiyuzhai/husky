pub mod domain;
pub mod extension;

pub use self::extension::*;

use super::*;

pub struct VfsTestConfig<'a> {
    test_name: &'a str,
    cargo_manifest_dir: PathBuf,
    expect_file_extension: FileExtensionConfig,
    test_domains_config: TestDomainsConfig,
}

/// # constructor
impl<'a> VfsTestConfig<'a> {
    pub fn new(
        test_name: &'a str,
        expect_file_extension: FileExtensionConfig,
        test_domains_config: TestDomainsConfig,
    ) -> Self {
        let paths = HuskyLangDevPaths::new();
        let cargo_manifest_dir = paths
            .cargo_manifest_dir()
            .map(|p| p.to_owned())
            .unwrap_or("temp".into());
        Self {
            test_name,
            cargo_manifest_dir,
            expect_file_extension,
            test_domains_config,
        }
    }
}

/// # getters
impl<'a> VfsTestConfig<'a> {
    pub fn test_name(&self) -> &str {
        self.test_name
    }

    pub fn cargo_manifest_dir(&self) -> &Path {
        &self.cargo_manifest_dir
    }

    pub fn expect_file_extension(&self) -> FileExtensionConfig {
        self.expect_file_extension
    }

    pub fn adversarial_extension(&self) -> &str {
        ADVERSARIAL_EXTENSION
    }

    pub fn test_domains_config(&self) -> &TestDomainsConfig {
        &self.test_domains_config
    }

    pub(super) fn test_domains(&self) -> Vec<TestDomain> {
        self.test_domains_config
            .test_domains(&self.cargo_manifest_dir)
    }
}
