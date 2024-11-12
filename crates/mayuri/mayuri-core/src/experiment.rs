pub mod gene;

use std::path::Path;

use self::gene::ExperimentGene;
use crate::{
    src::{MayuriSrc, MayuriSrcFile},
    *,
};
use config::nemu::NemuConfig;
use husky_sha_utils::{Sha256Output, Sha512Output, ShaHash};
use husky_yaml_utils::ordered::OrderedYaml;
use makefile::MayuriMakefileExtracted;
use relative_path::{RelativePath, RelativePathBuf};
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::process::Command;
use vec_like::ordered_vec_map::OrderedVecPairMap;
use yaml_rust2::Yaml;

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct Experiment {
    gene: ExperimentGene,
    gene_sha_str: String,
    protein: ExperimentProtein,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct ExperimentProtein {
    src_files: ExperimentSrcFiles,
    config: OrderedYaml,
    makefile: MayuriMakefileExtracted,
}

pub type ExperimentSrcFiles = OrderedVecPairMap<RelativePathBuf, MayuriSrcFile>;

impl Experiment {
    pub(super) fn new(
        yaml: &Yaml,
        src: &MayuriSrc,
        makefile: MayuriMakefileExtracted,
        nemu_config: &NemuConfig,
    ) -> Self {
        let config = OrderedYaml::new(yaml["config"].clone());
        let path = ExperimentGene::new(yaml, config.clone(), nemu_config);
        let src_files: ExperimentSrcFiles = nemu_config
            .src_paths()
            .iter()
            .map(|src_path| {
                (
                    RelativePath::new(src_path.path()).to_relative_path_buf(),
                    src[src_path.path_str()].clone(),
                )
            })
            .chain(
                yaml["src"]
                    .as_hash()
                    .expect("expected hash")
                    .iter()
                    .map(|(k, v)| {
                        (
                            RelativePath::new(k.as_str().expect("invalid yaml, expected string"))
                                .to_relative_path_buf(),
                            src[v.as_str().expect("invalid, expected string")].clone(),
                        )
                    }),
            )
            .collect();

        Self {
            gene_sha_str: Self::truncated_sha256(&path),
            gene: path,
            protein: ExperimentProtein {
                src_files,
                config,
                makefile,
            },
        }
    }

    fn truncated_sha256(path: &ExperimentGene) -> String {
        let full_sha = path.sha256().hex();

        // Create a 64-bit hash from the full SHA-256 string
        let hash_64bit = Self::hash_string_to_u64(&full_sha);

        // Convert the 64-bit hash to a 16-character hexadecimal string
        format!("{:016x}", hash_64bit)
    }

    fn hash_string_to_u64(s: &str) -> u64 {
        let mut hasher = DefaultHasher::new();
        s.hash(&mut hasher);
        hasher.finish()
    }
}

impl Experiment {
    pub fn run_local(&self, dir: &Path, name: Option<&str>) {
        use std::fs::{self, File};
        use std::io::Write;
        use std::path::Path;

        let workdir = &match name {
            Some(n) => dir.join(format!("{}-{}", n, self.gene_sha_str)),
            None => dir.join(&self.gene_sha_str),
        };

        // Write makefile to the workdir
        let makefile_path = workdir.join("makefile");
        fs::create_dir_all(&workdir).expect("Failed to create workdir");
        let mut makefile = File::create(makefile_path).expect("Failed to create makefile");
        makefile
            .write_all(self.protein.makefile.content().to_string().as_bytes())
            .expect("Failed to write makefile content");

        for (dest, src_file) in &self.protein.src_files {
            let dest_path = dest.to_logical_path(workdir);
            // Path::new(dest);

            // Create parent directories if they don't exist
            if let Some(parent) = dest_path.parent() {
                fs::create_dir_all(parent).expect("Failed to create parent directories");
            }
            let content = &src_file.content;
            let mut file = File::create(dest_path).expect("Failed to create destination file");
            file.write_all(content.as_bytes())
                .expect("Failed to write content to file");
        }

        // Run "cd workdir && make run"
        let output = Command::new("sh")
            .arg("-c")
            .arg(format!("cd '{}' && make run", workdir.display()))
            .output()
            .expect("Failed to execute command");

        if !output.status.success() {
            eprintln!("Command failed:");
            eprintln!("{}", String::from_utf8_lossy(&output.stderr));
        } else {
            println!("Command succeeded:");
            println!("{}", String::from_utf8_lossy(&output.stdout));
        }
    }
}
