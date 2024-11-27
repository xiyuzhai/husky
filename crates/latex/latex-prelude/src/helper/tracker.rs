use crate::mode::LxMode;
use latex_vfs::path::LxFilePath;
use std::path::{Path, PathBuf};

pub trait IsLxInput<'a>: Copy {
    fn specs_dir(self) -> &'a Path;
    fn latex_complete_commands_path(self) -> PathBuf {
        self.specs_dir().join("latex/complete-commands.lpcsv")
    }
    fn content(self) -> &'a str;
    fn root_mode(self) -> LxMode;
    fn file_path(self) -> LxFilePath;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LxDocumentInput<'a> {
    pub specs_dir: &'a Path,
    pub file_path: LxFilePath,
    pub content: &'a str,
}

impl<'a> IsLxInput<'a> for LxDocumentInput<'a> {
    fn specs_dir(self) -> &'a Path {
        self.specs_dir
    }

    fn file_path(self) -> LxFilePath {
        self.file_path
    }

    fn content(self) -> &'a str {
        self.content
    }

    fn root_mode(self) -> LxMode {
        LxMode::Root
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LxDocumentBodyInput<'a> {
    pub specs_dir: &'a Path,
    pub file_path: LxFilePath,
    pub content: &'a str,
}

impl<'a> IsLxInput<'a> for LxDocumentBodyInput<'a> {
    fn specs_dir(self) -> &'a Path {
        self.specs_dir
    }

    fn file_path(self) -> LxFilePath {
        self.file_path
    }

    fn content(self) -> &'a str {
        self.content
    }

    fn root_mode(self) -> LxMode {
        LxMode::Rose
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LxPageInput<'a> {
    pub specs_dir: &'a Path,
    pub file_path: LxFilePath,
    pub content: &'a str,
}

impl<'a> IsLxInput<'a> for LxPageInput<'a> {
    fn specs_dir(self) -> &'a Path {
        self.specs_dir
    }

    fn file_path(self) -> LxFilePath {
        self.file_path
    }

    fn content(self) -> &'a str {
        self.content
    }

    fn root_mode(self) -> LxMode {
        LxMode::Rose
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LxFormulaInput<'a> {
    pub specs_dir: &'a Path,
    pub file_path: LxFilePath,
    pub content: &'a str,
}

impl<'a> IsLxInput<'a> for LxFormulaInput<'a> {
    fn specs_dir(self) -> &'a Path {
        self.specs_dir
    }

    fn file_path(self) -> LxFilePath {
        self.file_path
    }

    fn content(self) -> &'a str {
        self.content
    }

    fn root_mode(self) -> LxMode {
        LxMode::Math
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LxLispInput<'a> {
    pub specs_dir: &'a Path,
    pub file_path: LxFilePath,
    pub content: &'a str,
}

impl<'a> IsLxInput<'a> for LxLispInput<'a> {
    fn specs_dir(self) -> &'a Path {
        self.specs_dir
    }

    fn file_path(self) -> LxFilePath {
        self.file_path
    }

    fn content(self) -> &'a str {
        self.content
    }
    fn root_mode(self) -> LxMode {
        LxMode::Lisp
    }
}
