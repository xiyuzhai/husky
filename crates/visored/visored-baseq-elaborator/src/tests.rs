use crate::{
    elaborator::{VdBsqElaborator, VdBsqElaboratorInner},
    helpers::tracker::VdBsqElaboratorTracker,
    session::VdBsqSession,
    *,
};
use eterned::db::EternerDb;
use husky_path_utils::search::find_files;
use latex_prelude::helper::tracker::LxDocumentInput;
use latex_vfs::path::LxFilePath;
use std::{
    marker::PhantomData,
    path::{Path, PathBuf},
    sync::Arc,
};
use visored_global_dispatch::default_table::VdDefaultGlobalDispatchTable;
use visored_lean_transpilation::scheme::dense::VdLeanTranspilationDenseScheme;
use visored_models::VdModels;
use visored_syn_expr::vibe::VdSynExprVibe;

#[test]
fn visored_tactic_baseq_elaborator_works() {
    use husky_case_utils::{Case, ToCase};
    use husky_path_utils::HuskyLangDevPaths;

    fn t(
        dev_paths: &HuskyLangDevPaths,
        src_root: &Path,
        src_file_paths: Vec<PathBuf>,
        lean4_dir: &Path,
        expect_files_dir: &Path,
    ) {
        let db = &EternerDb::default();
        for src_file_path in src_file_paths {
            use expect_test::expect_file;
            use relative_path::PathExt;

            let relative_path = src_file_path
                .relative_to(src_root)
                .unwrap()
                .to_case(Case::Pascal)
                .with_extension("lean");
            let content = std::fs::read_to_string(&src_file_path).unwrap();
            let dispatch_table =
                Arc::new(VdDefaultGlobalDispatchTable::from_standard_lisp_csv_file_dir(db));
            let session = &VdBsqSession::new(db, dispatch_table);
            let tracker = VdBsqElaboratorTracker::new(
                LxDocumentInput {
                    specs_dir: dev_paths.specs_dir().to_path_buf(),
                    file_path: LxFilePath::new(src_file_path, db),
                    content: &content,
                },
                &[],
                &[],
                &VdModels {},
                VdSynExprVibe::ROOT_CNL,
                db,
                |region_data| VdBsqElaborator::new(VdBsqElaboratorInner::new(session, region_data)),
                &VdLeanTranspilationDenseScheme,
            );
            let lean4_code: String = format!(
                r#"import Mathlib
import Visored.Tactics

set_option maxHeartbeats 20000000000

{}"#,
                tracker.show_fmt(db)
            );
            let expect_file_path = relative_path.to_logical_path(lean4_dir);
            assert!(
                expect_file_path.exists(),
                "Expect file path does not exist: {:?}",
                expect_file_path
            );
            expect_file!(expect_file_path).assert_eq(&lean4_code);
        }
    }

    let dev_paths = HuskyLangDevPaths::new();
    let specs_dir = dev_paths.specs_dir();
    // Collect all .tex files from the directory
    let src_root = &PathBuf::from("latex/main");
    let tex_files = find_files(src_root, |p| {
        p.extension().map_or(false, |ext| ext == "tex")
    })
    .unwrap();
    let lean4_dir = &dev_paths
        .lean4_lib_dir()
        .join("visored/Visored/BaseqElaborator/Tests/Main");
    t(
        &dev_paths,
        src_root,
        tex_files,
        lean4_dir,
        Path::new("../expect-files/visored-pipeline-works"),
    );
}
