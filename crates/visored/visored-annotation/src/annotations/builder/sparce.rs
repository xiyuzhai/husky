use super::*;
use crate::{
    annotation::{space::VdSpaceAnnotation, token::VdTokenAnnotation},
    annotations::{
        VdAnnotationRecord, VdAnnotations, VdSpaceAnnotationRecord, VdTokenAnnotationRecord,
    },
};
use latex_ast::ast::LxAstArena;
use latex_token::storage::LxTokenStorage;

pub(crate) fn collect_from_sparse_annotations<'a>(
    raw_text: &'a str,
    token_annotation_iter: impl Iterator<Item = ((&'a str, &'a str), VdTokenAnnotation)>,
    space_annotation_iter: impl Iterator<Item = ((&'a str, &'a str), VdSpaceAnnotation)>,
    token_storage: &LxTokenStorage,
) -> VdAnnotations {
    let token_annotations = collect_from_sparse_token_annotations(raw_text, token_annotation_iter);
    let space_annotations = collect_from_sparse_space_annotations(raw_text, space_annotation_iter);

    VdAnnotations::new(token_annotations, space_annotations, token_storage)
}

fn collect_from_sparse_token_annotations<'a>(
    raw_text: &'a str,
    token_annotation_iter: impl Iterator<Item = ((&'a str, &'a str), VdTokenAnnotation)>,
) -> Vec<VdTokenAnnotationRecord> {
    collect_from_sparse_annotations_aux(raw_text, token_annotation_iter)
}

fn collect_from_sparse_space_annotations<'a>(
    raw_text: &'a str,
    space_annotation_iter: impl Iterator<Item = ((&'a str, &'a str), VdSpaceAnnotation)>,
) -> Vec<VdSpaceAnnotationRecord> {
    collect_from_sparse_annotations_aux(raw_text, space_annotation_iter)
}

fn collect_from_sparse_annotations_aux<'a, A>(
    raw_text: &'a str,
    annotation_iter: impl Iterator<Item = ((&'a str, &'a str), A)>,
) -> Vec<VdAnnotationRecord<A>> {
    let mut annotations = Vec::new();
    for ((prev_s, token_s), annotation) in annotation_iter {
        let start = prev_s.len();
        let end = prev_s.len() + token_s.len();
        assert_eq!(&raw_text[..start], prev_s);
        assert_eq!(&raw_text[start..end], token_s);
        annotations.push(VdAnnotationRecord {
            offset_range: (start..end).into(),
            annotation,
        });
    }
    annotations
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::annotation::{
        space::LxApplyAnnotation,
        token::{LxIntegralAnnotation, LxVariableAnnotation},
    };
    use expect_test::expect;
    use latex_ast::ast::parse_latex_input_into_asts;
    use latex_command::signature::table::LxCommandSignatureTable;
    use latex_environment::signature::table::LxEnvironmentSignatureTable;
    use latex_prelude::mode::LxMode;

    #[test]
    fn test_collect_from_sparse_annotations_integral() {
        let db = &DB::default();
        let input = "\\int xdx";
        let command_signature_table = LxCommandSignatureTable::new_default(db);
        let environment_signature_table = LxEnvironmentSignatureTable::new_default(db);
        let token_annotations = vec![
            (
                ("", "\\int"),
                VdTokenAnnotation::Integral(
                    LxIntegralAnnotation::SingleVariableIndefiniteIntegralOverReal,
                ),
            ),
            (
                ("\\int ", "x"),
                VdTokenAnnotation::Variable(LxVariableAnnotation::Usage),
            ),
            (("\\int x", "d"), VdTokenAnnotation::Differential),
            (
                ("\\int xd", "x"),
                VdTokenAnnotation::Variable(
                    LxVariableAnnotation::SingleVariableIntegralVariableDecl,
                ),
            ),
        ];

        let space_annotations = vec![(
            ("\\int x", "d"),
            VdSpaceAnnotation::Apply(LxApplyAnnotation::ScalarDifferentialFormMul),
        )];

        let mut token_storage = LxTokenStorage::default();
        let mut ast_arena = LxAstArena::default();
        let asts = parse_latex_input_into_asts(
            db,
            &command_signature_table,
            &environment_signature_table,
            input,
            LxMode::Math,
            &mut token_storage,
            &mut ast_arena,
        );

        let result = collect_from_sparse_annotations(
            input,
            token_annotations.iter().copied(),
            space_annotations.iter().copied(),
            &token_storage,
        );

        expect![[r#"
            VdAnnotations {
                token_annotation_records: [
                    VdAnnotationRecord {
                        offset_range: TextOffsetRange {
                            start: TextOffset(
                                0,
                            ),
                            end: TextOffset(
                                4,
                            ),
                        },
                        annotation: Integral(
                            SingleVariableIndefiniteIntegralOverReal,
                        ),
                    },
                    VdAnnotationRecord {
                        offset_range: TextOffsetRange {
                            start: TextOffset(
                                5,
                            ),
                            end: TextOffset(
                                6,
                            ),
                        },
                        annotation: Variable(
                            Usage,
                        ),
                    },
                    VdAnnotationRecord {
                        offset_range: TextOffsetRange {
                            start: TextOffset(
                                6,
                            ),
                            end: TextOffset(
                                7,
                            ),
                        },
                        annotation: Differential,
                    },
                    VdAnnotationRecord {
                        offset_range: TextOffsetRange {
                            start: TextOffset(
                                7,
                            ),
                            end: TextOffset(
                                8,
                            ),
                        },
                        annotation: Variable(
                            SingleVariableIntegralVariableDecl,
                        ),
                    },
                ],
                space_annotation_records: [
                    VdAnnotationRecord {
                        offset_range: TextOffsetRange {
                            start: TextOffset(
                                6,
                            ),
                            end: TextOffset(
                                7,
                            ),
                        },
                        annotation: Apply(
                            ScalarDifferentialFormMul,
                        ),
                    },
                ],
                token_annotations: [
                    Some(
                        Integral(
                            SingleVariableIndefiniteIntegralOverReal,
                        ),
                    ),
                    Some(
                        Variable(
                            Usage,
                        ),
                    ),
                    Some(
                        Differential,
                    ),
                    Some(
                        Variable(
                            SingleVariableIntegralVariableDecl,
                        ),
                    ),
                ],
                space_annotations: [
                    None,
                    None,
                    Some(
                        Apply(
                            ScalarDifferentialFormMul,
                        ),
                    ),
                    None,
                ],
            }
        "#]]
        .assert_debug_eq(&result);
    }
}
