use super::*;
use latex_prelude::mode::LxMode;

fn t(input: &str, expected_display_tree: &Expect, expected_fmt: &Expect) {
    let db = &DB::default();
    let example = VdLeanTranspilationExample::new(input, LxMode::Math, &[], &[], db);
    expected_display_tree.assert_eq(&example.show_display_tree(db));
    expected_fmt.assert_eq(&example.show_fmt(db));
}

#[test]
fn basic_visored_to_lean_works() {
    t(
        "1 + 1",
        &expect![[r#"
        binary: `+`
        ├─ literal: `1`
        └─ literal: `1`
    "#]],
        &expect!["1 + 1"],
    );
}

#[test]
fn item_to_lean_works() {
    t(
        "\\mathbb{N}",
        &expect![[r#"
            item path: `Nat`
        "#]],
        &expect!["Nat"],
    );
}
