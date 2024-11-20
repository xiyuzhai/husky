mod body;
mod document;
mod expr;
mod page;

use crate::{builder::VdLeanTranspilationBuilder, VdTranspileToLean, *};
use expect_test::{expect, Expect};
use visored_mir_expr::{builder::VdMirExprBuilder, ToVdMir};
use visored_opr::opr::binary::VdBaseBinaryOpr;
use visored_sem_expr::expr::{binary::VdSemBinaryDispatch, VdSemExprData};
use visored_term::menu::vd_ty_menu;

#[salsa::db(
    husky_coword::jar::CowordJar,
    latex_ast::jar::LxAstJar,
    latex_command::jar::LxCommandJar,
    latex_environment::jar::LxEnvironmentJar,
    latex_token::jar::LxTokenJar,
    lean_item_path::jar::LnItemPathJar,
    lean_term::jar::LnTermJar,
    lean_sem_expr::jar::LnSemExprJar,
    lean_mir_expr::jar::LnMirExprJar,
    visored_item_path::jar::VdItemPathJar,
    visored_term::jar::VdTermJar,
    visored_opr::jar::VdOprJar,
    visored_sem_expr::jar::VdSemExprJar,
    visored_mir_expr::jar::VdMirExprJar,
    visored_syn_expr::jar::VdSynExprJar,
    visored_global_dispatch::jar::VdGlobalDispatchJar,
    visored_signature::jar::VdSignatureJar,
    latex_vfs::jar::LxVfsJar,
    crate::Jar
)]
pub(crate) struct DB {}

// #[test]
// fn one_add_one_to_lean_works() {
//     let db = &DB::default();
//     let menu = vd_ty_menu(db);
//     let mut builder = VdSemExprTestBuilder::new(db);
//     let one = builder.new_expr_checked(
//         VdSemExprData::Literal {
//             literal: menu.one_literal(),
//             dispatch: VdSemLiteralDispatch::Int,
//         },
//         "1",
//     );
//     let one_add_one = builder.new_expr_checked(
//         VdSemExprData::Binary {
//             lopd: one,
//             opr: VdBaseBinaryOpr::Add,
//             ropd: one,
//             dispatch: VdSemBinaryDispatch::IntAdd,
//         },
//         "1+1",
//     );
//     let vd_sem_expr_region_data = &builder.finish();
//     let mut builder = VdMirExprBuilder::new(db, vd_sem_expr_region_data);
//     let one_add_one = one_add_one.to_hir(&mut builder);
//     let vd_mir_expr_region_data = &builder.finish();
//     let mut builder = VdLeanTranspilationBuilder::new(db, vd_mir_expr_region_data);
//     let one_add_one = one_add_one.to_lean(&mut builder);
//     let mut formatter = builder.formatter(80);
//     formatter.format_expr_ext(one_add_one);
//     assert_eq!(&formatter.finish(), "1 + 1");
// }

// #[test]
// fn one_add_one_eqs_two_to_lean_works() {
//     let db = &DB::default();
//     let menu = vd_ty_menu(db);
//     let mut builder = VdSemExprTestBuilder::new(db);
//     let one = builder.new_expr_checked(
//         VdSemExprData::Literal {
//             literal: menu.one_literal(),
//             dispatch: VdSemLiteralDispatch::Int,
//         },
//         "1",
//     );
//     let two = builder.new_expr_checked(
//         VdSemExprData::Literal {
//             literal: menu.two_literal(),
//             dispatch: VdSemLiteralDispatch::Int,
//         },
//         "2",
//     );
//     let one_add_one = builder.new_expr_checked(
//         VdSemExprData::Binary {
//             lopd: one,
//             opr: VdBaseBinaryOpr::Add,
//             ropd: one,
//             dispatch: VdSemBinaryDispatch::IntAdd,
//         },
//         "1+1",
//     );
//     let one_add_one_eqs_two = builder.new_expr_checked(
//         VdSemExprData::Binary {
//             lopd: one_add_one,
//             opr: VdBaseBinaryOpr::Eq,
//             ropd: two,
//             dispatch: VdSemBinaryDispatch::TrivialEq,
//         },
//         "1+1=2",
//     );
//     let vd_sem_expr_region_data = &builder.finish();
//     let mut builder = VdMirExprBuilder::new(db, vd_sem_expr_region_data);
//     let one_add_one = one_add_one_eqs_two.to_hir(&mut builder);
//     let vd_mir_expr_region_data = &builder.finish();
//     let mut builder = VdLeanTranspilationBuilder::new(db, vd_mir_expr_region_data);
//     let one_add_one = one_add_one.to_lean(&mut builder);
//     let mut formatter = builder.formatter(80);
//     formatter.format_expr_ext(one_add_one);
//     assert_eq!(&formatter.finish(), "1 + 1 = 2");
// }
