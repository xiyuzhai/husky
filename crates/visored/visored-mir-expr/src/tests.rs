use crate::{builder::VdMirExprBuilder, ToVdMir};
use visored_opr::opr::binary::VdBaseBinaryOpr;
use visored_sem_expr::expr::{binary::VdSemBinaryDispatch, VdSemExprData};
use visored_term::menu::vd_ty_menu;

#[salsa::db(
    husky_coword::jar::CowordJar,
    latex_ast::jar::LxAstJar,
    latex_command::jar::LxCommandJar,
    latex_environment::jar::LxEnvironmentJar,
    latex_token::jar::LxTokenJar,
    visored_item_path::jar::VdItemPathJar,
    visored_term::jar::VdTermJar,
    visored_opr::jar::VdOprJar,
    visored_sem_expr::jar::VdSemExprJar,
    visored_syn_expr::jar::VdSynExprJar,
    visored_global_dispatch::jar::VdGlobalDispatchJar,
    visored_signature::jar::VdSignatureJar,
    latex_vfs::jar::LxVfsJar,
    crate::jar::VdMirExprJar
)]
pub(crate) struct DB {}
