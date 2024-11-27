mod body;
mod document;
mod expr;
mod page;

pub(crate) use expect_test::*;

// #[test]
// fn one_add_one_to_lean_works() {
//     let db = &DB::default();
//     let menu = VD_TYPE_MENU();
//     let mut builder = VdSemExprTestBuilder::new();
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
//     let mut builder = VdMirExprBuilder::new(vd_sem_expr_region_data);
//     let one_add_one = one_add_one.to_hir(&mut builder);
//     let vd_mir_expr_region_data = &builder.finish();
//     let mut builder = VdLeanTranspilationBuilder::new(vd_mir_expr_region_data);
//     let one_add_one = one_add_one.to_lean(&mut builder);
//     let mut formatter = builder.formatter(80);
//     formatter.format_expr_ext(one_add_one);
//     assert_eq!(&formatter.finish(), "1 + 1");
// }

// #[test]
// fn one_add_one_eqs_two_to_lean_works() {
//     let db = &DB::default();
//     let menu = VD_TYPE_MENU();
//     let mut builder = VdSemExprTestBuilder::new();
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
//     let mut builder = VdMirExprBuilder::new(vd_sem_expr_region_data);
//     let one_add_one = one_add_one_eqs_two.to_hir(&mut builder);
//     let vd_mir_expr_region_data = &builder.finish();
//     let mut builder = VdLeanTranspilationBuilder::new(vd_mir_expr_region_data);
//     let one_add_one = one_add_one.to_lean(&mut builder);
//     let mut formatter = builder.formatter(80);
//     formatter.format_expr_ext(one_add_one);
//     assert_eq!(&formatter.finish(), "1 + 1 = 2");
// }
