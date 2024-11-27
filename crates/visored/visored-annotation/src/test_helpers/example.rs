use super::*;
use crate::{
    annotation::{
        space::{LxApplyAnnotation, VdSpaceAnnotation},
        token::{LxVariableAnnotation, VdTokenAnnotation},
    },
    annotations::VdAnnotations,
};
use latex_ast::ast::{parse_latex_input_into_asts, LxAstArena};
use latex_command::signature::table::LxCommandSignatureTable;
use latex_environment::signature::table::LxEnvironmentSignatureTable;
use latex_prelude::mode::LxMode;
use latex_token::{lane::LxTokenLane, storage::LxTokenStorage};
use lazy_static::lazy_static;

#[derive(Debug, Clone)]
pub struct VdAnnotationsExample {
    pub input: String,
    pub root_mode: LxMode,
    pub annotations: VdAnnotations,
}

impl VdAnnotationsExample {
    fn collect_from_sparse(
        examples: &[(
            LxMode,
            &str,
            &[((&str, &str), VdTokenAnnotation)],
            &[((&str, &str), VdSpaceAnnotation)],
        )],
    ) -> Vec<Self> {
        todo!()
        // let command_signature_table = LxCommandSignatureTable::new_default();
        // let environment_signature_table = LxEnvironmentSignatureTable::new_default();
        // examples
        //     .iter()
        //     .map(
        //         |&(root_mode, input, token_annotations, space_annotations)| {
        //             let mut token_storage = LxTokenStorage::default();
        //             let mut ast_arena = LxAstArena::default();
        //             let asts = parse_latex_input_into_asts(
        //                 &db,
        //                 &command_signature_table,
        //                 &environment_signature_table,
        //                 &input,
        //                 LxTokenLane::Main,
        //                 LxMode::Math,
        //                 &mut token_storage,
        //                 &mut ast_arena,
        //             );
        //             let mut ast_arena = LxAstArena::default();
        //             let asts = parse_latex_input_into_asts(
        //                 &db,
        //                 &command_signature_table,
        //                 &environment_signature_table,
        //                 &input,
        //                 LxTokenLane::Main,
        //                 LxMode::Math,
        //                 &mut token_storage,
        //                 &mut ast_arena,
        //             );
        //             let annotations = VdAnnotations::from_sparse(
        //                 input,
        //                 token_annotations.iter().copied(),
        //                 space_annotations.iter().copied(),
        //                 &token_storage,
        //             );
        //             Self {
        //                 root_mode,
        //                 input: input.to_string(),
        //                 annotations,
        //             }
        //         },
        //     )
        //     .collect()
    }
}

pub fn lx_annotations_examples() -> Vec<VdAnnotationsExample> {
    use crate::annotation::{space::*, token::*};

    VdAnnotationsExample::collect_from_sparse(&[
        (LxMode::Math, "", &[], &[]),
        (
            LxMode::Math,
            "xy",
            &[(("", "x"), VARIABLE_USAGE), (("x", "y"), VARIABLE_USAGE)],
            &[(("x", "y"), SCALAR_MUL)],
        ),
        (
            LxMode::Math,
            "dx",
            &[
                (("", "d"), DIFFERENTIAL),
                (("d", "x"), SINGLE_VARIABLE_INTEGRAL_VARIABLE_DECL),
            ],
            &[],
        ),
    ])
}

#[test]
#[ignore]
fn latex_annotations_examples_works() {
    let examples = lx_annotations_examples();
    expect_test::expect_file!["../../expect-files/annotations/examples.txt"]
        .assert_eq(&format!("{:#?}", examples));
}
