pub mod config;
pub mod error;
pub mod file_sync;
pub mod read;
pub mod relative_path_pattern;
pub use config::*;

use husky_print_utils::p;
use relative_path::{RelativePath, RelativePathBuf};
use std::{
    collections::HashMap,
    fs,
    path::{Path, PathBuf},
};

// first read and compare, and then write if necessary
// TODO: add error handling
pub fn diff_write(path: impl AsRef<Path>, content: impl AsRef<str>, verbose: bool) {
    let path = path.as_ref();
    let content = content.as_ref();
    let necessary = match fs::read_to_string(path) {
        Ok(content_on_disk) => content != content_on_disk,
        Err(_) => true,
    };
    if necessary {
        match std::fs::create_dir_all(path.parent().unwrap()) {
            Ok(_) => (),
            Err(_) => todo!(),
        };
        if verbose {
            use husky_print_utils::*;
            println!(
                "{GREEN}updating{RESET} path `{}`",
                path.as_os_str().to_str().unwrap()
            );
        }
        match fs::write(path, content) {
            Ok(_) => (),
            Err(e) => {
                p!(path, e);
                todo!()
            }
        }
    }
}

// first read and compare, and then write if different
pub fn diff_copy(src: &Path, dst: &Path, verbose: bool) {
    let content = fs::read_to_string(src).unwrap();
    diff_write(dst, &content, verbose)
}
