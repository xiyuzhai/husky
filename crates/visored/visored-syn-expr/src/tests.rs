#[salsa::db(
    husky_coword::jar::CowordJar,
    visored_term::jar::VdTermJar,
    latex_token::jar::LxTokenJar,
    latex_ast::jar::LxAstJar,
    latex_command::jar::LxCommandJar,
    latex_environment::jar::LxEnvironmentJar,
    visored_opr::jar::VdOprJar,
    visored_item_path::jar::VdItemPathJar,
    latex_vfs::jar::LxVfsJar,
    crate::jar::VdSynExprJar
)]
pub(crate) struct DB {}
