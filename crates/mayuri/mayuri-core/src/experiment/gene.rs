use super::*;

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct ExperimentGene {
    src_paths: ExperimentSrcOriginPaths,
    config: OrderedYaml,
}

/// maps destination paths to origin paths
pub type ExperimentSrcOriginPaths = OrderedVecPairMap<String, String>;

impl ExperimentGene {
    pub fn new(yaml: &Yaml, config: OrderedYaml, nemu_config: &NemuConfig) -> Self {
        Self {
            src_paths: nemu_config
                .src_paths()
                .iter()
                .map(|src_path| (src_path.path().to_string(), src_path.path().to_string()))
                .chain(
                    yaml["src"]
                        .as_hash()
                        .expect("expected hash")
                        .iter()
                        .map(|(k, v)| {
                            (
                                k.as_str()
                                    .expect("invalid yaml, expected string")
                                    .to_string(),
                                v.as_str().expect("invalid, expected string").to_string(),
                            )
                        }),
                )
                .collect(),
            config,
        }
    }
}
