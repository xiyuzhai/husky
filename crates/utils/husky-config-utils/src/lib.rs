use serde::{Deserialize, Serialize};
use std::path::PathBuf;
use std::{fs, io};

pub trait IsConfig: Sized {
    fn read_from_toml_file(path: &PathBuf) -> io::Result<Self>;
}

// Default implementation for types that implement TomlConfig and Deserialize
impl<T: for<'de> Deserialize<'de>> IsConfig for T {
    fn read_from_toml_file(path: &PathBuf) -> io::Result<Self> {
        let content = fs::read_to_string(path)?;
        toml::from_str(&content).map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
    }
}
