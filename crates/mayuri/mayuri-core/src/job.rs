//! # Job YAML Format
//!
//! ```yaml
//! ---
//! name: <job_name>           # Name of the job (string)
//! src:                       # Source file mappings
//!     <target>: <source>     # Map target files to source files
//!     ...
//! config:                    # Job configuration
//!     <key>: <value>         # Key-value pairs for job parameters
//!     ...                    # Additional key-value pairs can be added
//! ---
//! # Additional jobs follow the same structure, separated by '---'
//! ```
//!
//! This YAML format defines multiple jobs in a single file. Each job
//! specifies a name, source file mappings, and a flexible configuration section.
//! Jobs are separated by `---`.
//!
//! ## Examples
//!
//! ### Single Job
//!
//! ```yaml
//! ---
//! name: simple-nn-job
//! src:
//!     "model.py": "models/neural_network.py"
//!     "data.py": "datasets/mnist.py"
//! config:
//!     epochs: 10
//!     learning_rate: 0.001
//!     batch_size: 32
//! ```
//!
//! ### Multiple Jobs
//!
//! ```yaml
//! ---
//! name: cnn-small-job
//! src:
//!     "model.py": "models/cnn.py"
//!     "data.py": "datasets/cifar10.py"
//! config:
//!     epochs: 20
//!     layers: [32, 64]
//!     dropout: 0.5
//!
//! ---
//! name: cnn-large-job
//! src:
//!     "model.py": "models/cnn.py"
//!     "data.py": "datasets/cifar10.py"
//! config:
//!     epochs: 50
//!     layers: [64, 128, 256]
//!     dropout: 0.3
//! ```

use crate::{
    config::nemu::NemuConfig, experiment::Experiment, makefile::MayuriMakefileExtracted,
    src::MayuriSrc, *,
};
use husky_yaml_utils::ordered::OrderedYaml;
use serde::Deserialize;
use std::path::PathBuf;
use yaml_rust2::Yaml;

#[derive(Debug)]
pub struct MayuriJob {
    path: PathBuf,
    rank: usize,
    experiment: Experiment,
}

impl MayuriJob {
    pub(super) fn read_from_file<'a>(
        path: PathBuf,
        src: &'a MayuriSrc,
        makefile: &'a MayuriMakefileExtracted,
        nemu_config: &'a NemuConfig,
    ) -> impl Iterator<Item = Self> + 'a {
        let contents = std::fs::read_to_string(&path).expect("Failed to read the YAML file");

        let docs = yaml_rust2::YamlLoader::load_from_str(&contents).expect("Failed to parse YAML");
        docs.into_iter().enumerate().map(move |(rank, yaml)| {
            Self::new(path.clone(), rank, yaml, src, makefile, nemu_config)
        })
    }

    fn new(
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
        }
    }
}

#[derive(Debug)]
pub struct MayuriJobs {
    jobs: Vec<MayuriJob>,
}

impl MayuriJobs {
    pub(crate) fn from_dir(
        dir: PathBuf,
        src: &MayuriSrc,
        makefile: &MayuriMakefileExtracted,
        nemu_config: &NemuConfig,
    ) -> MayuriJobs {
        let mut jobs = Vec::new();

        if let Ok(entries) = std::fs::read_dir(dir) {
            for entry in entries.flatten() {
                if let Ok(file_type) = entry.file_type() {
                    if file_type.is_file() {
                        let path = entry.path();
                        if let Some(extension) = path.extension() {
                            if extension == "yaml" || extension == "yml" {
                                jobs.extend(MayuriJob::read_from_file(
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

        Self { jobs }
    }

    pub(crate) fn run_all(&self) {
        self.jobs.iter().for_each(|job| job.run());
    }
}

impl MayuriJob {
    fn run(&self) {
        todo!()
    }
}
