use std::collections::HashSet;
use std::fmt;
use std::fs;
use std::fs::File;
use std::ops::{Deref, DerefMut};
use std::path::Path;

pub mod extract;
pub mod parse;

pub struct Makefile(makefile_lossless::Makefile);

impl fmt::Display for Makefile {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl Deref for Makefile {
    type Target = makefile_lossless::Makefile;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Makefile {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl Makefile {
    pub(crate) fn new() -> Self {
        Makefile(makefile_lossless::Makefile::new())
    }
}
