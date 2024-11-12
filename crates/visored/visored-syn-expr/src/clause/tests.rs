use super::*;
use crate::test_helpers::example::VdSynExprExample;
use expect_test::{expect, Expect};
use latex_prelude::mode::LxMode;
use visored_annotation::annotation::{space::VdSpaceAnnotation, token::VdTokenAnnotation};

fn t(
    input: &str,
    token_annotations: &[((&str, &str), VdTokenAnnotation)],
    space_annotations: &[((&str, &str), VdSpaceAnnotation)],
    expected: &Expect,
) {
    use crate::helpers::show::display_tree::VdSynExprDisplayTreeBuilder;

    let db = &DB::default();
    let example = VdSynExprExample::new(
        input,
        LxMode::Rose,
        token_annotations,
        space_annotations,
        db,
    );
    expected.assert_eq(&example.show_display_tree(db));
}

#[test]
fn let_clause_parsing_works() {
    t(
        "Let $x = 1$.",
        &[],
        &[],
        &expect![[r#"
            Let $x = 1$.
            └─ "Let $x = 1$." stmt.paragraph
              └─ "Let $x = 1$." sentence.clauses
                └─ "Let $x = 1$" clause.let
                  └─ "x = 1" expr.separated_list
                    ├─ "x" expr.letter
                    └─ "1" expr.literal
        "#]],
    );
    t(
        "Let $x \\in \\mathbb{N}$.",
        &[],
        &[],
        &expect![[r#"
            Let $x \in \mathbb{N}$.
            └─ "Let $x \\in \\mathbb{N}$." stmt.paragraph
              └─ "Let $x \\in \\mathbb{N}$." sentence.clauses
                └─ "Let $x \\in \\mathbb{N}$" clause.let
                  └─ "x \\in \\mathbb{N}" expr.separated_list
                    ├─ "x" expr.letter
                    └─ "\\mathbb{N}" expr.letter
        "#]],
    );
}
