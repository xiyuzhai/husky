pub mod lock;

use lock::RichTestLock;
use salsa::DebugWithDb;

use super::*;
use std::collections::HashMap;

/// includes adversarial
pub(super) fn vfs_rich_test<DB, M, U>(f: impl Fn(&::salsa::Db, U) -> String, config: &VfsTestConfig)
where
    DB: VfsTestUtils,
    U: IsVfsTestUnit<M> + salsa::DebugWithDb,
{
    let mut lock = RichTestLock::new(config);
    for test_domain in config.test_domains() {
        for package_relative_dir in
            collect_package_relative_dirs(&test_domain.src_base()).into_iter()
        {
            let db = &mut *DB::default();
            let toolchain = db.dev_toolchain().unwrap();
            let package_path = PackagePath::new_local_or_toolchain_package(
                db,
                toolchain,
                &package_relative_dir.to_logical_path(&test_domain.src_base()),
            )
            .unwrap();
            let units = collect_units_from_package_path::<M, U>(db, package_path);
            for unit in units {
                let output = f(db, unit);
                let output = match config.expect_file_extension() {
                    FileExtensionConfig::Markdown => format!("```rust\n{output}\n```"),
                    FileExtensionConfig::Rust => output,
                };
                lock.insert(
                    unit.determine_expect_unit_path(
                        db,
                        &package_relative_dir.to_logical_path(&test_domain.expect_files_base()),
                        config,
                    ),
                    output.clone(),
                );
                if let Some(adversarials_base) = test_domain.adversarials_base() {
                    let adversarial_path = package_relative_dir.to_logical_path(adversarials_base);
                    vfs_adversarial_test(db, &adversarial_path, unit, &f, config, &mut lock)
                }
            }
        }
    }
}
