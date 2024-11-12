#[salsa::db(
    husky_coword::jar::CowordJar,
    visored_zfc_ty::jar::VdZfcTypeJar,
    visored_opr::jar::VdOprJar,
    latex_ast::jar::LxAstJar,
    latex_command::jar::LxCommandJar,
    latex_environment::jar::LxEnvironmentJar,
    crate::jar::VdSemExprJar,
    visored_syn_expr::jar::VdSynExprJar
)]
pub(crate) struct DB {}
