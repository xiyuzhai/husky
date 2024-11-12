use super::*;
use super::*;
use crate::test_helpers::example::VdSemExprExample;
use expect_test::{expect, Expect};
use latex_prelude::mode::LxMode;

pub(crate) fn t(input: &str, expected: &Expect) {
    let db = &DB::default();
    let example = VdSemExprExample::new(input, LxMode::Math, &[], &[], db);
    expected.assert_eq(&example.show_display_tree(db))
}

#[test]
pub(crate) fn basic_vd_sem_expr_works() {
    t(
        "1+1",
        &expect![[r#"
        "1+1" expr.separated_list
        ├─ "1" expr.literal
        └─ "1" expr.literal
    "#]],
    );
    t(
        "1+1=2",
        &expect![[r#"
            "1+1=2" expr.separated_list
            ├─ "1+1" expr.separated_list
            │ ├─ "1" expr.literal
            │ └─ "1" expr.literal
            └─ "2" expr.literal
        "#]],
    );
}
