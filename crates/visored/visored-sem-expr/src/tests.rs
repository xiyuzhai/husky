#[salsa::db(
    husky_coword::jar::CowordJar,
    latex_ast::jar::LxAstJar,
    latex_token::jar::LxTokenJar,
    latex_command::jar::LxCommandJar,
    latex_environment::jar::LxEnvironmentJar,
    latex_vfs::jar::LxVfsJar,
    visored_term::jar::VdTermJar,
    visored_opr::jar::VdOprJar,
    visored_syn_expr::jar::VdSynExprJar,
    visored_item_path::jar::VdItemPathJar,
    visored_global_dispatch::jar::VdGlobalDispatchJar,
    visored_signature::jar::VdSignatureJar,
    crate::jar::VdSemExprJar
)]
pub(crate) struct DB {}
