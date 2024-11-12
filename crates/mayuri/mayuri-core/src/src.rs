use husky_sha_utils::{Sha512Output, ShaHash};
// use rustc_hash::FxHashMap;
use std::ops::Index;
use std::path::{Path, PathBuf};
use std::{collections::BTreeMap, fs};
use std::{collections::HashMap, sync::Arc};
use vec_like::ordered_vec_map::OrderedVecPairMap;
use walkdir::WalkDir;

#[derive(Debug)]
pub struct MayuriSrc {
    dir_path: PathBuf,
    files: BTreeMap<String, MayuriSrcFile>,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct MayuriSrcFile {
    pub content: Arc<String>,
}

impl MayuriSrcFile {
    fn from_file<P: AsRef<Path>>(path: P) -> std::io::Result<Self> {
        let content = Arc::new(fs::read_to_string(path)?);
        Ok(MayuriSrcFile { content })
    }
}

impl MayuriSrc {
    pub fn new(dir_path: PathBuf, allowed_exts: &[&str]) -> Result<Self, std::io::Error> {
        let mut files = BTreeMap::default();

        for entry in WalkDir::new(&dir_path).into_iter().filter_map(|e| e.ok()) {
            let path = entry.path();
            if path.is_file()
                && path
                    .extension()
                    .and_then(|ext| ext.to_str())
                    .map_or(false, |ext| allowed_exts.contains(&ext))
            {
                let relative_path = path
                    .strip_prefix(&dir_path)
                    .unwrap()
                    .to_str()
                    .unwrap()
                    .to_string();
                let src_file = MayuriSrcFile::from_file(path)?;
                let sha = src_file.content.as_bytes().sha512();
                files.insert(relative_path, src_file);
            }
        }

        Ok(Self { dir_path, files })
    }
}

impl Index<&str> for MayuriSrc {
    type Output = MayuriSrcFile;

    fn index(&self, key: &str) -> &Self::Output {
        self.files.get(key).unwrap_or_else(|| {
            panic!(
                "Source file not found: {} in directory: {}",
                key,
                self.dir_path.display()
            )
        })
    }
}
