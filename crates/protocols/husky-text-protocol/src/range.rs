use crate::*;

use serde::{Deserialize, Serialize};

#[derive(Default, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TextPositionRange {
    pub start: TextPosition,
    pub end: TextPosition,
}

impl TextPositionRange {
    pub fn join(self, other: Self) -> Self {
        Self {
            start: self.start,
            end: other.end,
        }
    }

    /// returns the text range after `self` in the same line
    /// ```
    /// use husky_text_protocol::range::TextPositionRange;
    ///
    /// let a: TextPositionRange = ((0,0)..(0,3)).into();
    /// let b: TextPositionRange = ((0,3)..(0,4)).into();
    /// assert_eq!(a.right_after(), b)
    /// ```
    pub fn right_after(self) -> Self {
        Self {
            start: self.end,
            end: self.end.to_right(1),
        }
    }
}

#[cfg(feature = "lsp_support")]
impl From<lsp_types::Range> for TextPositionRange {
    fn from(range: lsp_types::Range) -> Self {
        Self {
            start: range.start.into(),
            end: range.end.into(),
        }
    }
}

impl TextPositionRange {
    pub fn closed_end(&self) -> TextPosition {
        self.end.to_left(1)
    }
    pub fn intersects(self, other: Self) -> bool {
        self.start < other.end && other.start < self.end
    }
}

impl std::fmt::Display for TextPositionRange {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{} - {}", self.start, self.end))
    }
}

impl std::fmt::Debug for TextPositionRange {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("[{}, {})", self.start, self.end))
    }
}

impl TextPositionRange {
    pub fn whole() -> TextPositionRange {
        ((0, 0)..(0, 4)).into()
    }

    pub fn from_line(line: u32) -> TextPositionRange {
        ((line, 0)..(line, 4)).into()
    }

    pub fn from_u32(range: std::ops::Range<(u32, u32)>) -> Self {
        range.into()
    }

    pub fn is_within(&self, other: &Self) -> bool {
        self.start >= other.start && self.end <= other.end
    }
}

impl From<std::ops::Range<(u32, u32)>> for TextPositionRange {
    fn from(range: std::ops::Range<(u32, u32)>) -> Self {
        Self {
            start: range.start.into(),
            end: range.end.into(),
        }
    }
}

impl From<std::ops::Range<TextPosition>> for TextPositionRange {
    fn from(range: std::ops::Range<TextPosition>) -> Self {
        Self {
            start: range.start,
            end: range.end,
        }
    }
}

#[cfg(feature = "lsp_support")]
impl Into<lsp_types::Range> for TextPositionRange {
    fn into(self) -> lsp_types::Range {
        lsp_types::Range::new(self.start.into(), self.end.into())
    }
}

pub fn new_same_line(i: u32, start: u32, end: u32) -> TextPositionRange {
    TextPositionRange {
        start: (i, start).into(),
        end: (i, end).into(),
    }
}

pub struct RangeInfo<T> {
    pub t: T,
    pub range: TextPositionRange,
}
