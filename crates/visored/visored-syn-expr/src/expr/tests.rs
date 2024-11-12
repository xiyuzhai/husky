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
        LxMode::Math,
        token_annotations,
        space_annotations,
        db,
    );
    expected.assert_eq(&example.show_display_tree(db));
}

#[test]
fn literal_vd_syn_expr_parsing_works() {
    t(
        "",
        &[],
        &[],
        &expect![[r#"
            "" expr.error
        "#]],
    );
    t(
        "1",
        &[],
        &[],
        &expect![[r#"
            "1" expr.literal
        "#]],
    );
    t(
        "11",
        &[],
        &[],
        &expect![[r#"
            "11" expr.literal
        "#]],
    );
    t(
        "1 1",
        &[],
        &[],
        &expect![[r#"
            "1 1" expr.separated_list
            ├─ "1" expr.literal
            └─ "1" expr.literal
        "#]],
    );
}

#[test]
fn basic_arithematics_vd_syn_expr_parsing_works() {
    t(
        "1 + 1",
        &[],
        &[],
        &expect![[r#"
            "1 + 1" expr.separated_list
            ├─ "1" expr.literal
            └─ "1" expr.literal
        "#]],
    );
    t(
        "1 + 1 = 2",
        &[],
        &[],
        &expect![[r#"
            "1 + 1 = 2" expr.separated_list
            ├─ "1 + 1" expr.separated_list
            │ ├─ "1" expr.literal
            │ └─ "1" expr.literal
            └─ "2" expr.literal
        "#]],
    );
    t(
        "1 + 1 = 2",
        &[],
        &[],
        &expect![[r#"
            "1 + 1 = 2" expr.separated_list
            ├─ "1 + 1" expr.separated_list
            │ ├─ "1" expr.literal
            │ └─ "1" expr.literal
            └─ "2" expr.literal
        "#]],
    );
}

#[test]
fn xyz_vd_syn_expr_parsing_works() {
    t(
        "x",
        &[],
        &[],
        &expect![[r#"
            "x" expr.letter
        "#]],
    );
    t(
        "y",
        &[],
        &[],
        &expect![[r#"
            "y" expr.letter
        "#]],
    );
    t(
        "z",
        &[],
        &[],
        &expect![[r#"
            "z" expr.letter
        "#]],
    );
    t(
        "xyz",
        &[],
        &[],
        &expect![[r#"
            "xyz" expr.separated_list
            ├─ "x" expr.letter
            ├─ "y" expr.letter
            └─ "z" expr.letter
        "#]],
    );
}

#[test]
fn arithemtics_with_xyz_vd_syn_expr_parsing_works() {
    t(
        "1+x",
        &[],
        &[],
        &expect![[r#"
            "1+x" expr.separated_list
            ├─ "1" expr.literal
            └─ "x" expr.letter
        "#]],
    );
    t(
        "1+2x",
        &[],
        &[],
        &expect![[r#"
            "1+2x" expr.separated_list
            ├─ "1" expr.literal
            └─ "2x" expr.separated_list
              ├─ "2" expr.literal
              └─ "x" expr.letter
        "#]],
    );
    t(
        "1+2xy",
        &[],
        &[],
        &expect![[r#"
            "1+2xy" expr.separated_list
            ├─ "1" expr.literal
            └─ "2xy" expr.separated_list
              ├─ "2" expr.literal
              ├─ "x" expr.letter
              └─ "y" expr.letter
        "#]],
    );
    t(
        "1+x+2xy",
        &[],
        &[],
        &expect![[r#"
            "1+x+2xy" expr.separated_list
            ├─ "1" expr.literal
            ├─ "x" expr.letter
            └─ "2xy" expr.separated_list
              ├─ "2" expr.literal
              ├─ "x" expr.letter
              └─ "y" expr.letter
        "#]],
    );
    t(
        "1+x+2",
        &[],
        &[],
        &expect![[r#"
            "1+x+2" expr.separated_list
            ├─ "1" expr.literal
            ├─ "x" expr.letter
            └─ "2" expr.literal
        "#]],
    );
    t(
        "1+x+2y",
        &[],
        &[],
        &expect![[r#"
            "1+x+2y" expr.separated_list
            ├─ "1" expr.literal
            ├─ "x" expr.letter
            └─ "2y" expr.separated_list
              ├─ "2" expr.literal
              └─ "y" expr.letter
        "#]],
    );
    t(
        "1+x+y+z+xyz",
        &[],
        &[],
        &expect![[r#"
            "1+x+y+z+xyz" expr.separated_list
            ├─ "1" expr.literal
            ├─ "x" expr.letter
            ├─ "y" expr.letter
            ├─ "z" expr.letter
            └─ "xyz" expr.separated_list
              ├─ "x" expr.letter
              ├─ "y" expr.letter
              └─ "z" expr.letter
        "#]],
    );
    t(
        "1+x+y+z+abc",
        &[],
        &[],
        &expect![[r#"
            "1+x+y+z+abc" expr.separated_list
            ├─ "1" expr.literal
            ├─ "x" expr.letter
            ├─ "y" expr.letter
            ├─ "z" expr.letter
            └─ "abc" expr.separated_list
              ├─ "a" expr.letter
              ├─ "b" expr.letter
              └─ "c" expr.letter
        "#]],
    );
}

#[test]
fn more_operators_with_xyz_vd_syn_expr_parsing_works() {
    t(
        "0\\ne1",
        &[],
        &[],
        &expect![[r#"
            "0\\ne1" expr.separated_list
            ├─ "0" expr.literal
            └─ "1" expr.literal
        "#]],
    );
    t(
        "0\\in\\mathbb{N}",
        &[],
        &[],
        &expect![[r#"
            "0\\in\\mathbb{N}" expr.separated_list
            ├─ "0" expr.literal
            └─ "\\mathbb{N}" expr.letter
        "#]],
    );
    t(
        "A\\subset B",
        &[],
        &[],
        &expect![[r#"
            "A\\subset B" expr.separated_list
            ├─ "A" expr.letter
            └─ "B" expr.letter
        "#]],
    );
    t(
        "A\\subseteq B",
        &[],
        &[],
        &expect![[r#"
            "A\\subseteq B" expr.separated_list
            ├─ "A" expr.letter
            └─ "B" expr.letter
        "#]],
    );
    t(
        "A\\subseteqq B",
        &[],
        &[],
        &expect![[r#"
            "A\\subseteqq B" expr.separated_list
            ├─ "A" expr.letter
            └─ "B" expr.letter
        "#]],
    );
    t(
        "A\\supseteq B",
        &[],
        &[],
        &expect![[r#"
            "A\\supseteq B" expr.separated_list
            ├─ "A" expr.letter
            └─ "B" expr.letter
        "#]],
    );
    t(
        "A\\supseteqq B",
        &[],
        &[],
        &expect![[r#"
            "A\\supseteqq B" expr.separated_list
            ├─ "A" expr.letter
            └─ "B" expr.letter
        "#]],
    );
    t(
        "A\\subsetneq B",
        &[],
        &[],
        &expect![[r#"
            "A\\subsetneq B" expr.separated_list
            ├─ "A" expr.letter
            └─ "B" expr.letter
        "#]],
    );
    t(
        "A\\supsetneq B",
        &[],
        &[],
        &expect![[r#"
            "A\\supsetneq B" expr.separated_list
            ├─ "A" expr.letter
            └─ "B" expr.letter
        "#]],
    );
}

#[test]
fn delimiters_vd_syn_expr_parsing_works() {
    t(
        "(1)",
        &[],
        &[],
        &expect![[r#"
            "(1)" delimited
            └─ "1" expr.literal
        "#]],
    );
}

#[test]
fn math_zero_argument_commands_vd_syn_expr_parsing_works() {
    t(
        "\\alpha",
        &[],
        &[],
        &expect![[r#"
            "\\alpha" expr.letter
        "#]],
    );
    t(
        "\\pi",
        &[],
        &[],
        &expect![[r#"
            "\\pi" expr.letter
        "#]],
    );
}

#[test]
fn math_commands_with_arguments_vd_syn_expr_parsing_works() {
    t(
        "\\frac{1}{2}",
        &[],
        &[],
        &expect![[r#"
            "\\frac{1}{2}" fraction
            ├─ "1" expr.literal
            └─ "2" expr.literal
        "#]],
    );
    t(
        "\\frac{x+1}{2-2y}",
        &[],
        &[],
        &expect![[r#"
            "\\frac{x+1}{2-2y}" fraction
            ├─ "x+1" expr.separated_list
            │ ├─ "x" expr.letter
            │ └─ "1" expr.literal
            └─ "2-2y" expr.binary
              ├─ "2" expr.literal
              └─ "2y" expr.separated_list
                ├─ "2" expr.literal
                └─ "y" expr.letter
        "#]],
    );
    t(
        "\\sqrt{1}",
        &[],
        &[],
        &expect![[r#"
            "\\sqrt{1}" sqrt
            └─ "1" expr.literal
        "#]],
    );
    t(
        "\\sqrt{x+1}",
        &[],
        &[],
        &expect![[r#"
            "\\sqrt{x+1}" sqrt
            └─ "x+1" expr.separated_list
              ├─ "x" expr.letter
              └─ "1" expr.literal
        "#]],
    );
    t(
        "\\sqrt{\\frac{1}{2+x}}",
        &[],
        &[],
        &expect![[r#"
            "\\sqrt{\\frac{1}{2+x}}" sqrt
            └─ "\\frac{1}{2+x}" fraction
              ├─ "1" expr.literal
              └─ "2+x" expr.separated_list
                ├─ "2" expr.literal
                └─ "x" expr.letter
        "#]],
    );
}

#[test]
fn opr_commands_vd_syn_expr_parsing_works() {
    use visored_annotation::annotation::token::DIFFERENTIAL;

    t(
        "\\int xdx",
        &[(("\\int x", "d"), DIFFERENTIAL)],
        &[],
        &expect![[r#"
            "\\int xdx" expr.prefix
            └─ "xdx" expr.separated_list
              ├─ "x" expr.letter
              └─ "dx" expr.prefix
                └─ "x" expr.letter
        "#]],
    )
}

#[test]
fn attach_vd_syn_expr_parsing_works() {
    t(
        "x^2",
        &[],
        &[],
        &expect![[r#"
            "x^2" expr.attach
            ├─ "x" expr.letter
            └─ "2" expr.literal
        "#]],
    );
    t(
        "{(x+1)}^2",
        &[],
        &[],
        &expect![[r#"
            "{(x+1)}^2" expr.attach
            ├─ "{(x+1)}" expr.latex_delimited
            │ └─ "(x+1)" delimited
            │   └─ "x+1" expr.separated_list
            │     ├─ "x" expr.letter
            │     └─ "1" expr.literal
            └─ "2" expr.literal
        "#]],
    );
}

#[test]
fn styled_letter_vd_syn_expr_parsing_works() {
    t(
        "\\mathbb{N}",
        &[],
        &[],
        &expect![[r#"
            "\\mathbb{N}" expr.letter
        "#]],
    );
}
