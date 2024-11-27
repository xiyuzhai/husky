use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};

#[derive(Debug, Serialize, Deserialize)]
pub struct Session {
    pub dir: PathBuf,
    pub port: u16,
}

impl Session {
    #[track_caller]
    pub fn load_from_yaml_file_path(path: &Path) -> Self {
        let content = match std::fs::read_to_string(path) {
            Ok(content) => content,
            Err(err) => panic!("Failed to read file at path {}: {}", path.display(), err),
        };
        // deserialize
        let session = serde_yaml::from_str(&content).unwrap();
        session
    }
}

#[test]
fn load_session_from_yaml_file_path_works() {
    use husky_path_utils::*;

    let dev_paths = HuskyLangDevPaths::new();
    let sessions_dir = dev_paths.sessions_dir();
    let mnist_session = Session::load_from_yaml_file_path(&sessions_dir.join("mnist.yaml"));
    let latex2lean_session =
        Session::load_from_yaml_file_path(&sessions_dir.join("latex2lean.yaml"));
}
