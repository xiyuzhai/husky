use crate::{error::*, *};

pub fn read_to_string(path: impl AsRef<Path>) -> IoResult<String> {
    std::fs::read_to_string(path.as_ref())
        .map_err(|_| IoError::Io(path.as_ref().to_path_buf(), "fail to read".to_string()))
}
