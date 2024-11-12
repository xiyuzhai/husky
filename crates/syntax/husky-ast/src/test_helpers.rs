pub use husky_token::test_helpers::*;

/// will have more adversarial tests based on token level information than `TokenTestUtils`
pub trait AstTestUtils: TokenTestUtils {
    /// only run to see whether the program will panic
    /// it will invoke adversarial test if environment variable `ADVERSARIAL_ROUND` is set be a positive number
    fn ast_plain_test<M, U>(f: impl Fn(&::salsa::Db, U), config: &AstTestConfig)
    where
        U: IsVfsTestUnit<M> + salsa::DebugWithDb;

    /// run to see whether the output agrees with previous
    /// it will invoke adversarial test if environment variable `ADVERSARIAL_ROUND` is set be a positive number
    fn ast_rich_test_debug_with_db<'a, M, U, R>(
        f: impl Fn(&'a ::salsa::Db, U) -> R,
        config: &AstTestConfig<'a>,
    ) where
        U: IsVfsTestUnit<M> + salsa::DebugWithDb,
        R: salsa::DebugWithDb;

    /// run to see whether the output agrees with previous
    /// it will invoke adversarial test if environment variable `ADVERSARIAL_ROUND` is set be a positive number
    fn ast_rich_test_debug<'a, M, U, R>(
        f: impl Fn(&'a ::salsa::Db, U) -> R,
        config: &AstTestConfig,
    ) where
        U: IsVfsTestUnit<M> + salsa::DebugWithDb,
        R: std::fmt::Debug;

    fn ast_rich_test_display<M, U, R>(f: impl Fn(&::salsa::Db, U) -> R, config: &AstTestConfig)
    where
        U: IsVfsTestUnit<M> + salsa::DebugWithDb,
        R: std::fmt::Display;
}

impl<DB> AstTestUtils for DB
where
    DB: TokenTestUtils,
{
    fn ast_plain_test<M, U>(f: impl Fn(&::salsa::Db, U), config: &AstTestConfig)
    where
        U: IsVfsTestUnit<M> + salsa::DebugWithDb,
    {
        // todo: robustness
        DB::token_plain_test(f, config)
    }

    fn ast_rich_test_debug_with_db<'a, M, U, R>(
        f: impl Fn(&'a ::salsa::Db, U) -> R,
        config: &AstTestConfig<'a>,
    ) where
        U: IsVfsTestUnit<M> + salsa::DebugWithDb,
        R: salsa::DebugWithDb,
    {
        // todo: robustness
        DB::token_rich_test_debug_with_db(f, &config.token)
    }

    fn ast_rich_test_debug<'a, M, U, R>(f: impl Fn(&'a ::salsa::Db, U) -> R, config: &AstTestConfig)
    where
        U: IsVfsTestUnit<M> + salsa::DebugWithDb,
        R: std::fmt::Debug,
    {
        // todo: robustness
        DB::token_rich_test_debug(f, &config.token)
    }

    fn ast_rich_test_display<M, U, R>(f: impl Fn(&::salsa::Db, U) -> R, config: &AstTestConfig)
    where
        U: IsVfsTestUnit<M> + salsa::DebugWithDb,
        R: std::fmt::Display,
    {
        // todo: robustness
        DB::token_rich_test_display(f, &config.token)
    }
}

pub struct AstTestConfig<'a> {
    token: TokenTestConfig<'a>,
}

impl<'a> AstTestConfig<'a> {
    pub fn new(
        test_name: &'a str,
        expect_file_extension: FileExtensionConfig,
        test_domains_config: TestDomainsConfig,
    ) -> Self {
        Self {
            token: TokenTestConfig::new(test_name, expect_file_extension, test_domains_config),
        }
    }
}

impl<'a> std::ops::Deref for AstTestConfig<'a> {
    type Target = TokenTestConfig<'a>;

    fn deref(&self) -> &Self::Target {
        &self.token
    }
}
