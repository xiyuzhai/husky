pub mod error;
pub mod expr;
pub mod file;
pub mod helpers;
mod parser;
pub mod row;
mod token;

use self::{error::*, expr::*, file::*, parser::*, row::*};
use either::*;
#[cfg(test)]
use expect_test::*;
use ordered_float::OrderedFloat;
use std::path::Path;

pub fn parse_lp_csv_filepath(path: &Path) -> LpCsvFileResult<LpCsvFile> {
    let s = std::fs::read_to_string(path).map_err(|error| LpCsvFileError::Io {
        file_path: path.to_path_buf(),
        error,
    })?;
    parse_lp_csv_file(&s).map_err(|error| LpCsvFileError::Parse { input: s, error })
}

pub fn parse_lp_csv_file(s: &str) -> Result<LpCsvFile, LpCsvError> {
    LpCsvParser::new(s).parse_file()
}
