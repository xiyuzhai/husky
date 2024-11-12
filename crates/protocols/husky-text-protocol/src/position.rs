mod column;
mod line;

pub use column::*;
pub use line::*;

use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};

#[derive(
    Debug, Default, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash, Serialize, Deserialize,
)]
pub struct TextPosition {
    pub line: TextLine,
    pub col: TextColumn,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct FilePosition {
    file: PathBuf,
    pos: TextPosition,
}

impl FilePosition {
    pub fn file(&self) -> &Path {
        &self.file
    }

    pub fn pos(&self) -> TextPosition {
        self.pos
    }
}

#[cfg(feature = "lsp_support")]
impl From<lsp_types::Position> for TextPosition {
    fn from(pos: lsp_types::Position) -> Self {
        Self {
            line: pos.line.into(),
            col: pos.character.into(),
        }
    }
}

impl From<(u32, u32)> for TextPosition {
    fn from(pair: (u32, u32)) -> Self {
        TextPosition {
            line: pair.0.into(),
            col: pair.1.into(),
        }
    }
}

impl From<&(u32, u32)> for TextPosition {
    fn from(pair: &(u32, u32)) -> Self {
        TextPosition {
            line: pair.0.into(),
            col: pair.1.into(),
        }
    }
}

// impl From<(usize, usize)> for TextPosition {
//     fn from(pair: (usize, usize)) -> Self {
//         TextPosition {
//             line: pair.0.into(),
//             col: pair.1.into(),
//         }
//     }
// }

// impl From<(i32, i32)> for TextPosition {
//     fn from(pair: (i32, i32)) -> Self {
//         TextPosition {
//             line: pair.0.into(),
//             col: pair.1.into(),
//         }
//     }
// }

impl TextPosition {
    pub fn one_based_line(&self) -> u32 {
        self.line.0 + 1
    }

    pub fn i(&self) -> u32 {
        self.line.0
    }
    pub fn j(&self) -> u32 {
        self.col.index32()
    }

    pub fn to_left(&self, x: u32) -> TextPosition {
        Self {
            line: self.line,
            col: self.col - x,
        }
    }

    pub fn to_right(&self, x: u32) -> TextPosition {
        Self {
            line: self.line,
            col: self.col + x,
        }
    }

    pub fn to_next_line(&self) -> TextPosition {
        Self {
            line: self.line.to_next_line(),
            col: Default::default(),
        }
    }
}

impl std::fmt::Display for TextPosition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!(
            "{:?}:{:?}",
            self.line.index() + 1,
            self.col.index() + 1
        ))
    }
}

#[cfg(feature = "lsp_support")]
impl From<TextPosition> for lsp_types::Position {
    fn from(val: TextPosition) -> Self {
        lsp_types::Position::new(val.line.index32(), val.col.index32())
    }
}
