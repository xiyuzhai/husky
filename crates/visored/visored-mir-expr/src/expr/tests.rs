use super::*;
use expect_test::{expect, Expect};
use helpers::tracker::VdMirExprTracker;
use latex_prelude::helper::tracker::LxFormulaInput;
use latex_prelude::mode::LxMode;
use latex_vfs::path::LxFilePath;
use std::path::PathBuf;

fn t(content: &str, expect: &Expect) {
    let db = &DB::default();
    let file_path = LxFilePath::new(db, PathBuf::from(file!()));
    let tracker = VdMirExprTracker::new(LxFormulaInput { file_path, content }, &[], &[], db);
    expect.assert_eq(&tracker.show_display_tree(db));
}

#[test]
fn basic_to_vd_mir_works() {
    t(
        "1 + 1",
        &expect![[r#"
            separator
            ├─ 1
            └─ 1
        "#]],
    );
    t(
        "1",
        &expect![[r#"
            1
        "#]],
    );
    t(
        "-1",
        &expect![[r#"
            prefix opr
            └─ 1
        "#]],
    );
    t(
        "1<2",
        &expect![[r#"
            separator
            ├─ 1
            └─ 2
        "#]],
    );
}

#[test]
fn frac_to_vd_mir_works() {
    t(
        "\\frac{1}{2}",
        &expect![[r#"
        frac
        ├─ 1
        └─ 2
    "#]],
    );
}

#[test]
fn sqrt_to_vd_mir_works() {
    t(
        "\\sqrt{1}",
        &expect![[r#"
        sqrt
        └─ 1
    "#]],
    );
}
