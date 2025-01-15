use super::*;
use crate::elaborator::VdMirTrivialElaborator;
use eterned::db::EternerDb;
use expect_test::{expect, Expect};
use helpers::tracker::VdMirExprTracker;
use latex_prelude::helper::tracker::LxDocumentBodyInput;
use latex_prelude::mode::LxMode;
use latex_vfs::path::LxFilePath;
use std::path::PathBuf;
use visored_syn_expr::vibe::VdSynExprVibe;

fn t(models: &VdModels, content: &str, expect: &Expect) {
    use husky_path_utils::HuskyLangDevPaths;

    let db = &EternerDb::default();
    let dev_paths = HuskyLangDevPaths::new();
    let file_path = LxFilePath::new(PathBuf::from(file!()), db);
    let tracker = VdMirExprTracker::new(
        LxDocumentBodyInput {
            specs_dir: dev_paths.specs_dir(),
            file_path,
            content,
        },
        &[],
        &[],
        models,
        VdSynExprVibe::ROOT_CNL,
        db,
        |_| VdMirTrivialElaborator::new(()),
    );
    expect.assert_eq(&tracker.show_display_tree(db));
}

#[test]
fn basic_body_to_vd_mir_works() {
    let models = &VdModels::new();
    t(
        models,
        r#"Let $x\in\mathbb{R}$."#,
        &expect![[r#"
            └─ block: Division(Blocks, VdModulePath(`root.stmts1`))
              ├─ let placeholder
              └─ qed
        "#]],
    );
    t(
        models,
        r#"\begin{example}\end{example}"#,
        &expect![[r#"
            └─ block: Division(Blocks, VdModulePath(`root.stmts1`))
              └─ block: Environment(LxEnvironmentPath { name: LxEnvironmentName(Coword("example")) }, Example, VdModulePath(`root.stmts1.example1`))
        "#]],
    );
    t(
        models,
        r#"\begin{example}Let $x\in\mathbb{R}$.\end{example}"#,
        &expect![[r#"
            └─ block: Division(Blocks, VdModulePath(`root.stmts1`))
              └─ block: Environment(LxEnvironmentPath { name: LxEnvironmentName(Coword("example")) }, Example, VdModulePath(`root.stmts1.example1`))
                ├─ let placeholder
                └─ qed
        "#]],
    );
}
