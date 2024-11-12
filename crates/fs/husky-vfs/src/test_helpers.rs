pub mod adversarial_test;
pub mod config;
pub mod domain;
pub mod jar;
pub mod rich_test;
pub mod unit;

pub use self::adversarial_test::*;
pub use self::config::*;
pub use self::domain::*;
pub use self::jar::*;
pub use self::unit::*;

use self::rich_test::*;
use crate::*;
use husky_path_utils::*;
use lock::RichTestLock;
use salsa::Db;
use std::{collections::HashMap, path::PathBuf};

pub trait VfsTestUtils: Default + std::ops::Deref<Target = Db> + std::ops::DerefMut {
    /// only run to see whether the program will panic
    /// it will invoke adversarial test if environment variable `ADVERSARIAL_ROUND` is set be a positive number
    fn vfs_plain_test<M, U>(f: impl Fn(&::salsa::Db, U), config: &VfsTestConfig)
    where
        U: IsVfsTestUnit<M> + salsa::DebugWithDb;

    /// run to see whether the output agrees with previous
    /// it will invoke adversarial test if environment variable `ADVERSARIAL_ROUND` is set be a positive number
    fn vfs_rich_test_debug_with_db<'a, M, U, R>(
        f: impl Fn(&'a ::salsa::Db, U) -> R,
        config: &VfsTestConfig,
    ) where
        U: IsVfsTestUnit<M> + salsa::DebugWithDb,
        R: salsa::DebugWithDb;

    /// run to see whether the output agrees with previous
    /// it will invoke adversarial test if environment variable `ADVERSARIAL_ROUND` is set be a positive number
    fn vfs_rich_test_debug<'a, M, U, R>(
        f: impl Fn(&'a ::salsa::Db, U) -> R,
        config: &VfsTestConfig,
    ) where
        U: IsVfsTestUnit<M> + salsa::DebugWithDb,
        R: std::fmt::Debug;

    fn vfs_rich_test_display<M, U, R>(f: impl Fn(&::salsa::Db, U) -> R, config: &VfsTestConfig)
    where
        U: IsVfsTestUnit<M> + salsa::DebugWithDb,
        R: std::fmt::Display;
}

const ADVERSARIAL_EXTENSION: &'static str = "json";

impl<DB> VfsTestUtils for DB
where
    DB: Default + std::ops::Deref<Target = Db> + std::ops::DerefMut,
{
    /// only run to see whether the program will panic
    /// it will invoke adversarial test if environment variable `ADVERSARIAL_ROUND` is set be a positive number
    fn vfs_plain_test<M, U>(f: impl Fn(&::salsa::Db, U), config: &VfsTestConfig)
    where
        U: IsVfsTestUnit<M> + ::salsa::DebugWithDb,
    {
        let mut paths_used: HashMap<PathBuf, PathUsage<U>> = Default::default();
        let mut lock = RichTestLock::new(config);
        for test_suite in config.test_domains() {
            for path in collect_package_relative_dirs(&test_suite.src_base()).into_iter() {
                let db = &mut *DB::default();
                let toolchain = db.dev_toolchain().unwrap();
                let package_path = PackagePath::new_local_or_toolchain_package(
                    db,
                    toolchain,
                    &path.to_logical_path(&test_suite.src_base()),
                )
                .unwrap();
                let units = collect_units_from_package_path::<M, U>(db, package_path);
                for unit in units {
                    f(db, unit);
                    if let Some(adversarials_base) = test_suite.adversarials_base() {
                        vfs_adversarial_test(
                            db,
                            &path.to_logical_path(adversarials_base),
                            unit,
                            &f,
                            config,
                            &mut lock,
                        )
                    }
                }
            }
        }
    }

    /// run to see whether the output agrees with previous
    /// it will invoke adversarial test if environment variable `ADVERSARIAL_ROUND` is set be a positive number
    fn vfs_rich_test_debug_with_db<'a, M, U, R>(
        f: impl Fn(&'a ::salsa::Db, U) -> R,
        config: &VfsTestConfig,
    ) where
        U: IsVfsTestUnit<M> + salsa::DebugWithDb,
        R: salsa::DebugWithDb,
    {
        vfs_rich_test::<DB, _, _>(
            |db, u| format!("{:#?}", &f(unsafe { std::mem::transmute(db) }, u).debug(db)),
            config,
        )
    }

    /// run to see whether the output agrees with previous
    /// it will invoke adversarial test if environment variable `ADVERSARIAL_ROUND` is set be a positive number
    fn vfs_rich_test_debug<'a, M, U, R>(f: impl Fn(&'a ::salsa::Db, U) -> R, config: &VfsTestConfig)
    where
        U: IsVfsTestUnit<M> + salsa::DebugWithDb,
        R: std::fmt::Debug,
    {
        vfs_rich_test::<DB, _, _>(
            |db, u| format!("{:#?}", &f(unsafe { std::mem::transmute(db) }, u)),
            config,
        )
    }

    fn vfs_rich_test_display<M, U, R>(f: impl Fn(&::salsa::Db, U) -> R, config: &VfsTestConfig)
    where
        U: IsVfsTestUnit<M> + salsa::DebugWithDb,
        R: std::fmt::Display,
    {
        vfs_rich_test::<DB, _, _>(|db, u| format!("{}", &f(db, u)), config)
    }
}

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq)]
enum PathUsage<U> {
    Expect(U),
    Adversarial(U),
}
