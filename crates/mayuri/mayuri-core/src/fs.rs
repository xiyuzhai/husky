use crate::{
    config::{mayuri::MayuriConfig, nemu::NemuConfig},
    job::{MayuriJob, MayuriJobs},
    makefile::MayuriMakefileExtracted,
    src::MayuriSrc,
    test::{MayuriTest, MayuriTests},
    *,
};
use git::set_up_gitignore;
use husky_config_utils::IsConfig;
use std::env;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

#[derive(Debug)]
pub struct MayuriFs {
    root: PathBuf,
    src: MayuriSrc,
    makefile: MayuriMakefileExtracted,
    jobs: MayuriJobs,
    tests: MayuriTests,
    /// read from `<root>/Mayuri.toml`
    mayuri_config: MayuriConfig,
    /// read from `<root>/Nemu.toml`
    nemu_config: NemuConfig,
}

impl MayuriFs {
    pub fn new(root: PathBuf, append: bool) -> Self {
        set_up_gitignore(&root, append);
        let mayuri_config = match MayuriConfig::read_from_toml_file(&root.join("Mayuri.toml")) {
            Ok(config) => config,
            Err(e) => panic!("Failed to read Mayuri.toml in {:?}: {}", root, e),
        };

        let nemu_config = match NemuConfig::read_from_toml_file(&root.join("Nemu.toml")) {
            Ok(config) => config,
            Err(e) => panic!("Failed to read Nemu.toml in {:?}: {}", root, e),
        };

        let src = match MayuriSrc::new(root.join("src"), &["py"]) {
            Ok(src) => src,
            Err(e) => panic!("Failed to create MayuriSrc in {:?}: {}", root, e),
        };
        let makefile = MayuriMakefileExtracted::new(&root, ["run".to_string()])
            .unwrap_or_else(|e| panic!("Failed to extract Makefile rules: {}", e));
        let jobs = MayuriJobs::from_dir(root.join("jobs"), &src, &makefile, &nemu_config);
        let tests = MayuriTests::from_dir(root.join("tests"), &src, &makefile, &nemu_config);
        MayuriFs {
            root,
            makefile,
            src,
            mayuri_config,
            nemu_config,
            jobs,
            tests,
        }
    }

    pub fn root(&self) -> &Path {
        &self.root
    }

    pub fn src(&self) -> &MayuriSrc {
        &self.src
    }

    pub fn makefile(&self) -> &MayuriMakefileExtracted {
        &self.makefile
    }

    pub fn jobs(&self) -> &MayuriJobs {
        &self.jobs
    }

    pub fn tests(&self) -> &MayuriTests {
        &self.tests
    }

    pub fn mayuri_config(&self) -> &MayuriConfig {
        &self.mayuri_config
    }

    pub fn nemu_config(&self) -> &NemuConfig {
        &self.nemu_config
    }

    pub fn run_all_tests(&self) {
        self.tests.run_all(&self.root.join("tests/.local"))
    }

    pub fn run_all_jobs(&self) {
        self.jobs.run_all()
    }
}

#[test]
fn mayuri_fs_works() {
    use husky_path_utils::HuskyLangDevPaths;
    use std::env;
    use std::path::Path;

    let dev_paths = HuskyLangDevPaths::new();
    let root = dev_paths.root();

    // Change the current working directory to the root
    env::set_current_dir(&root).unwrap();

    // Use a relative path from the root
    let mayuri_prototype_dir = Path::new("experiments/mayuri-prototype");

    // Now the current directory is the root, so we use the relative path
    let fs = MayuriFs::new(mayuri_prototype_dir.to_path_buf(), false);
    expect_test::expect_file!["../expect-files/mayuri_fs_works1.md"]
        .assert_eq(&format!("```rust\n{:#?}\n```", fs));
    fs.run_all_tests();
    // fs.run_all_jobs();
}
