pub use husky_vfs::test_helpers::*;

/// will have more adversarial tests based on token level information than `VfsTestUtils`
pub trait TokenTestUtils: VfsTestUtils {
    /// only run to see whether the program will panic
    /// it will invoke adversarial test if environment variable `ADVERSARIAL_ROUND` is set be a positive number
    fn token_plain_test<M, U>(f: impl Fn(&::salsa::Db, U), config: &VfsTestConfig)
    where
        U: IsVfsTestUnit<M> + salsa::DebugWithDb;

    /// run to see whether the output agrees with previous
    /// it will invoke adversarial test if environment variable `ADVERSARIAL_ROUND` is set be a positive number
    fn token_rich_test_debug_with_db<'a, M, U, R>(
        f: impl Fn(&'a ::salsa::Db, U) -> R,
        config: &TokenTestConfig<'a>,
    ) where
        U: IsVfsTestUnit<M> + salsa::DebugWithDb,
        R: salsa::DebugWithDb;

    /// run to see whether the output agrees with previous
    /// it will invoke adversarial test if environment variable `ADVERSARIAL_ROUND` is set be a positive number
    fn token_rich_test_debug<'a, M, U, R>(
        f: impl Fn(&'a ::salsa::Db, U) -> R,
        config: &TokenTestConfig,
    ) where
        U: IsVfsTestUnit<M> + salsa::DebugWithDb,
        R: std::fmt::Debug;

    fn token_rich_test_display<M, U, R>(f: impl Fn(&::salsa::Db, U) -> R, config: &TokenTestConfig)
    where
        U: IsVfsTestUnit<M> + salsa::DebugWithDb,
        R: std::fmt::Display;
}

impl<DB> TokenTestUtils for DB
where
    DB: VfsTestUtils,
{
    fn token_plain_test<M, U>(f: impl Fn(&::salsa::Db, U), config: &VfsTestConfig)
    where
        U: IsVfsTestUnit<M> + salsa::DebugWithDb,
    {
        // todo: robustness
        DB::vfs_plain_test(f, config);
    }

    fn token_rich_test_debug_with_db<'a, M, U, R>(
        f: impl Fn(&'a ::salsa::Db, U) -> R,
        config: &TokenTestConfig<'a>,
    ) where
        U: IsVfsTestUnit<M> + salsa::DebugWithDb,
        R: salsa::DebugWithDb,
    {
        // todo: robustness
        DB::vfs_rich_test_debug_with_db(f, &config.vfs)
    }

    fn token_rich_test_debug<'a, M, U, R>(
        f: impl Fn(&'a ::salsa::Db, U) -> R,
        config: &TokenTestConfig,
    ) where
        U: IsVfsTestUnit<M> + salsa::DebugWithDb,
        R: std::fmt::Debug,
    {
        // todo: robustness
        DB::vfs_rich_test_debug(&f, &config.vfs)
    }

    fn token_rich_test_display<M, U, R>(f: impl Fn(&::salsa::Db, U) -> R, config: &TokenTestConfig)
    where
        U: IsVfsTestUnit<M> + salsa::DebugWithDb,
        R: std::fmt::Display,
    {
        // todo: robustness
        DB::vfs_rich_test_display(&f, &config.vfs)
    }
}

pub struct TokenTestConfig<'a> {
    vfs: VfsTestConfig<'a>,
}

impl<'a> std::ops::Deref for TokenTestConfig<'a> {
    type Target = VfsTestConfig<'a>;

    fn deref(&self) -> &Self::Target {
        &self.vfs
    }
}

impl<'a> TokenTestConfig<'a> {
    pub fn new(
        test_name: &'a str,
        expect_file_extension: FileExtensionConfig,
        test_domains_config: TestDomainsConfig,
    ) -> Self {
        Self {
            vfs: VfsTestConfig::new(test_name, expect_file_extension, test_domains_config),
        }
    }
}
