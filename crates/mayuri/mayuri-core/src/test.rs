//! # Test YAML Format
//!
//! ```yaml
//! ---
//! name: <test_name>          # Name of the test (string)
//! src:                       # Source file mappings
//!     <target>: <source>     # Map target files to source files
//!     ...
//! config:                    # Test configuration
//!     <key>: <value>         # Key-value pairs for test parameters
//!     ...                    # Additional key-value pairs can be added
//! ---
//! # Additional tests follow the same structure, separated by '---'
//! ```
//!
//! This YAML format defines multiple tests in a single file. Each test
//! specifies a name, source file mappings, and a flexible configuration section.
//! Tests are separated by `---`.
//!
//! ## Examples
//!
//! ### Single Test
//!
//! ```yaml
//! ---
//! name: unit-test-1
//! src:
//!     "test_model.py": "tests/test_neural_network.py"
//!     "model.py": "models/neural_network.py"
//! config:
//!     test_cases: 5
//!     timeout: 30
//!     use_gpu: false
//! ```
//!
//! ### Multiple Tests
//!
//! ```yaml
//! ---
//! name: integration-test-1
//! src:
//!     "test_pipeline.py": "tests/test_data_pipeline.py"
//!     "data.py": "datasets/mnist.py"
//! config:
//!     dataset_size: 1000
//!     batch_size: 32
//!
//! ---
//! name: performance-test-1
//! src:
//!     "benchmark.py": "tests/benchmark_cnn.py"
//!     "model.py": "models/cnn.py"
//! config:
//!     iterations: 100
//!     warmup_rounds: 5
//!     profile_memory: true
//! ```

use crate::*;
use config::nemu::NemuConfig;
use experiment::Experiment;
use makefile::MayuriMakefileExtracted;
use src::MayuriSrc;
use std::path::{Path, PathBuf};
use yaml_rust2::Yaml;

#[derive(Debug)]
pub struct MayuriTest {
    path: PathBuf,
    name: String,
    rank: usize,
    experiment: Experiment,
}

impl MayuriTest {
    pub(super) fn from_file<'a>(
        path: PathBuf,
        src: &'a MayuriSrc,
        makefile: &'a MayuriMakefileExtracted,
        nemu_config: &'a NemuConfig,
    ) -> impl Iterator<Item = Self> + 'a {
        let contents = std::fs::read_to_string(&path).expect("Failed to read the YAML file");

        let docs = yaml_rust2::YamlLoader::load_from_str(&contents).expect("Failed to parse YAML");
        docs.into_iter().enumerate().map(move |(rank, yaml)| {
            Self::from_file_aux(path.clone(), rank, yaml, src, makefile, nemu_config)
        })
    }

    fn from_file_aux(
        path: PathBuf,
        rank: usize,
        yaml: Yaml,
        src: &MayuriSrc,
        makefile: &MayuriMakefileExtracted,
        nemu_config: &NemuConfig,
    ) -> Self {
        Self {
            path,
            rank,
            experiment: Experiment::new(&yaml, src, makefile.clone(), nemu_config),
            name: yaml["name"].as_str().unwrap().to_string(),
        }
    }
}

#[derive(Debug)]
pub struct MayuriTests {
    tests: Vec<MayuriTest>,
}

impl MayuriTests {
    pub(crate) fn from_dir(
        dir: PathBuf,
        src: &MayuriSrc,
        makefile: &MayuriMakefileExtracted,
        nemu_config: &NemuConfig,
    ) -> MayuriTests {
        let mut subjects = Vec::new();

        if let Ok(entries) = std::fs::read_dir(dir) {
            for entry in entries.flatten() {
                if let Ok(file_type) = entry.file_type() {
                    if file_type.is_file() {
                        let path = entry.path();
                        if let Some(extension) = path.extension() {
                            if extension == "yaml" || extension == "yml" {
                                subjects.extend(MayuriTest::from_file(
                                    path,
                                    src,
                                    makefile,
                                    nemu_config,
                                ));
                            }
                        }
                    }
                }
            }
        }

        Self { tests: subjects }
    }

    pub(crate) fn run_all(&self, tests_local_dir: &Path) {
        self.tests.iter().for_each(|test| test.run(tests_local_dir));
    }
}

impl MayuriTest {
    fn run(&self, tests_local_dir: &Path) {
        self.experiment.run_local(tests_local_dir, Some(&self.name))
    }
}
