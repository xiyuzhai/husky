#[salsa::db(
    husky_coword::jar::CowordJar,
    latex_token::jar::LxTokenJar,
    latex_ast::jar::LxAstJar,
    latex_command::jar::LxCommandJar,
    latex_environment::jar::LxEnvironmentJar,
    latex_vfs::jar::LxVfsJar
)]
pub(crate) struct DB;
