use super::VfsTestConfig;
use indexmap::IndexMap;
use rustc_hash::FxHashMap;
use std::fmt::{self, Display};
use std::{fs::File, io::Write, path::PathBuf};

pub struct RichTestLock {
    lock_path: PathBuf,
    lock_file: Option<File>,
    expect_file_contents: FxHashMap<PathBuf, ExpectFileContent>,
}

pub enum ExpectFileContent {
    Single(String),
    Sections(IndexMap<String, String>),
}

impl Display for ExpectFileContent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExpectFileContent::Single(content) => write!(f, "{}", content),
            ExpectFileContent::Sections(sections) => {
                for (i, (section, content)) in sections.iter().enumerate() {
                    if i > 0 {
                        writeln!(f)?;
                    }
                    writeln!(f, "## {}\n\n{}", section, content)?;
                }
                Ok(())
            }
        }
    }
}

impl RichTestLock {
    pub fn new(config: &VfsTestConfig) -> Self {
        let lock_path = config
            .cargo_manifest_dir()
            .join(config.test_name())
            .with_extension("rich-test-lock");
        let lock_file = if std::env::var("UPDATE_EXPECT").is_ok() {
            Some(match std::fs::File::create_new(&lock_path) {
                Ok(lock_file) => lock_file,
                Err(e) => panic!(
                    "failed to lock path `{:?}` for task `{}` due to {e}",
                    lock_path,
                    config.test_name()
                ),
            })
        } else {
            None
        };
        Self {
            lock_path,
            lock_file,
            expect_file_contents: Default::default(),
        }
    }
}

impl std::ops::Drop for RichTestLock {
    fn drop(&mut self) {
        for (path, content) in &self.expect_file_contents {
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            let output = content.to_string();
            ::expect_test::expect_file![path].assert_eq(&output)
        }
        if let Some(ref mut lock_file) = self.lock_file {
            for (path, content) in &self.expect_file_contents {
                lock_file.write(path.to_string_lossy().as_bytes()).unwrap();
                lock_file.write(b"\n");
            }
        }
    }
}

#[derive(Debug)]
pub enum ExpectUnitPath {
    Single(PathBuf),
    Sections(PathBuf, String),
}

impl ExpectUnitPath {
    pub fn with_section(self, section_name: String) -> ExpectUnitPath {
        match self {
            ExpectUnitPath::Single(path) => ExpectUnitPath::Sections(path, section_name),
            ExpectUnitPath::Sections(_, _) => unreachable!(),
        }
    }

    pub fn with_section_suffix(self, suffix: &str) -> ExpectUnitPath {
        match self {
            ExpectUnitPath::Single(path) => unreachable!(),
            ExpectUnitPath::Sections(path, section_name) => {
                ExpectUnitPath::Sections(path, format!("{} {}", section_name, suffix))
            }
        }
    }
}

impl RichTestLock {
    pub(super) fn insert(&mut self, path: ExpectUnitPath, content: String) {
        match path {
            ExpectUnitPath::Single(single_path) => {
                if self.expect_file_contents.contains_key(&single_path) {
                    panic!("Entry for path already exists");
                }
                self.expect_file_contents
                    .insert(single_path, ExpectFileContent::Single(content));
            }
            ExpectUnitPath::Sections(sections_path, section_name) => {
                match self.expect_file_contents.get_mut(&sections_path) {
                    Some(ExpectFileContent::Sections(sections)) => {
                        if sections.contains_key(&section_name) {
                            panic!("Section already exists for the given path");
                        }
                        sections.insert(section_name, content);
                    }
                    _ => {
                        let mut new_sections = IndexMap::new();
                        new_sections.insert(section_name, content);
                        self.expect_file_contents
                            .insert(sections_path, ExpectFileContent::Sections(new_sections));
                    }
                }
            }
        }
    }
}
