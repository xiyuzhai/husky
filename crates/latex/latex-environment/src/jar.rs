use crate::path::LxEnvironmentPath;

#[salsa::jar]
pub struct LxEnvironmentJar(crate::path::menu::lx_environment_path_menu);
