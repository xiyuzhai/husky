use crate::{
    fmt::RUSTFMT, manifest::linktime_target_rust_workspace_manifest,
    package::rust_transpilation_packages,
};
use husky_corgi_config::transpilation_setup::TranspilationSetup;
use husky_io_utils::error::IoResult;
use husky_vfs::path::linktime_target_path::LinktimeTargetPath;
use is::Is;

pub trait TranspileToFsFull: Is<LinktimeTargetPath> {
    /// transpile the target crate and its dependencies
    fn transpile_to_fs_full(self, setup: TranspilationSetup, db: &::salsa::Db) -> IoResult<()>;
}

impl TranspileToFsFull for LinktimeTargetPath {
    fn transpile_to_fs_full(self, setup: TranspilationSetup, db: &::salsa::Db) -> IoResult<()> {
        husky_io_utils::diff_write(self.rust_workspace_rustfmt_toml_path(db), RUSTFMT, true);
        husky_io_utils::diff_write(
            self.rust_workspace_manifest_path(db),
            linktime_target_rust_workspace_manifest(db, self),
            true,
        );
        for package in rust_transpilation_packages(db, self) {
            package.transpile_to_fs(setup, db)?
        }
        Ok(())
    }
}
