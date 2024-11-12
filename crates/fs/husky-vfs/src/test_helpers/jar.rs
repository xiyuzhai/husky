use super::*;
use crate::path::menu::VfsPathMenu;
use jar::VfsDb;

pub trait VfsTestUtilsDb {
    // toolchain
    fn dev_toolchain(&self) -> ToolchainResult<Toolchain>;

    fn dev_path_menu(&self) -> ToolchainResult<&VfsPathMenu>;
}

impl VfsTestUtilsDb for Db {
    // toolchain
    fn dev_toolchain(&self) -> ToolchainResult<Toolchain> {
        let library_path = find_lang_dev_library_path()?;
        Ok(Toolchain::new(
            self,
            ToolchainData::Local {
                library_path: VirtualPath::try_new(self, &library_path).unwrap(),
            },
        ))
    }

    fn dev_path_menu(&self) -> ToolchainResult<&VfsPathMenu> {
        let toolchain = self.dev_toolchain()?;
        Ok(self.vfs_path_menu(toolchain))
    }
}
