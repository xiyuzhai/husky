use crate::runner::VdPipelineRunner;
use alien_seed::AlienSeed;
use eterned::db::EternerDb;
use std::{
    path::{Path, PathBuf},
    sync::Arc,
};

#[test]
fn visored_pipeline_works() {
    use husky_path_utils::HuskyLangDevPaths;

    fn t(
        tokio_runtime: Arc<tokio::runtime::Runtime>,
        src_root: &Path,
        // TODO: replace with preloaded specs???
        specs_dir: &Path,
        lean4_dir: &Path,
        config_path: PathBuf,
        src_file_paths: Vec<PathBuf>,
        expect_files_dir: &Path,
    ) {
        let db = &EternerDb::default();
        let mut runner = VdPipelineRunner::new(
            db,
            tokio_runtime,
            specs_dir,
            lean4_dir,
            config_path,
            src_file_paths,
            src_root,
        )
        .unwrap();
        let seed = AlienSeed::new(0);
        runner.run_all_single_threaded(seed).unwrap();
        let latex_files = runner.export_result_latex_files(src_root).unwrap();
        for latex_file in latex_files {
            use expect_test::expect_file;

            expect_file!(latex_file.relative_path.to_logical_path(expect_files_dir))
                .assert_eq(&latex_file.latex_content);
        }
    }

    let tokio_runtime = Arc::new(tokio::runtime::Runtime::new().unwrap());
    let husky_lang_dev_paths = HuskyLangDevPaths::new();
    let specs_dir = husky_lang_dev_paths.specs_dir();
    // Collect all .tex files from the directory
    let src_root = &PathBuf::from("tests-data/visored-pipeline-works");
    let config_path = PathBuf::from("tests-data/visored-pipeline-works/config.yaml");
    let tex_files: Vec<PathBuf> = std::fs::read_dir(&src_root)
        .unwrap()
        .filter_map(|entry| {
            let entry = entry.ok()?;
            let path = entry.path();
            if path.extension()? == "tex" {
                Some(path)
            } else {
                None
            }
        })
        .collect();
    assert!(!tex_files.is_empty());
    let lean4_dir = &HuskyLangDevPaths::new()
        .lean4_lib_dir()
        .join("visored/Visored/Pipeline/Tests");

    t(
        tokio_runtime,
        src_root,
        specs_dir,
        lean4_dir,
        config_path,
        tex_files,
        Path::new("../expect-files/visored-pipeline-works"),
    );
}
