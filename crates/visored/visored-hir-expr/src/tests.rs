use crate::{builder::VdHirExprBuilder, ToVdHir};
use visored_opr::opr::binary::VdBaseBinaryOpr;
use visored_sem_expr::{
    expr::{binary::VdSemBinaryDispatch, VdSemExprData},
    test_helpers::builder::VdSemExprTestBuilder,
};
use visored_zfc_ty::menu::vd_zfc_ty_menu;

#[salsa::db(
    husky_coword::jar::CowordJar,
    latex_ast::jar::LxAstJar,
    latex_command::jar::LxCommandJar,
    latex_environment::jar::LxEnvironmentJar,
    visored_zfc_ty::jar::VdZfcTypeJar,
    visored_opr::jar::VdOprJar,
    visored_sem_expr::jar::VdSemExprJar,
    visored_syn_expr::jar::VdSynExprJar,
    crate::jar::VdHirExprJar
)]
pub(crate) struct DB {}
