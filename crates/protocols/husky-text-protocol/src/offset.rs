use std::ops::{Range, RangeFrom, RangeTo};

use serde::{Deserialize, Serialize};
use shifted_unsigned_int::ShiftedU32;

/// Character byte offset (zero-based). The meaning of this
/// offset is determined by the negotiated `PositionEncodingKind`.
#[derive(
    Debug, PartialEq, Default, Eq, PartialOrd, Ord, Clone, Copy, Hash, Serialize, Deserialize,
)]
#[serde(transparent)]
pub struct TextOffset(ShiftedU32);

impl std::fmt::Display for TextOffset {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.index())
    }
}

impl TextOffset {
    pub fn index(self) -> usize {
        self.0.index()
    }
}

impl From<i32> for TextOffset {
    fn from(raw: i32) -> Self {
        TextOffset(ShiftedU32::from(raw))
    }
}

impl From<usize> for TextOffset {
    fn from(raw: usize) -> Self {
        TextOffset(ShiftedU32::from(raw))
    }
}

impl From<u32> for TextOffset {
    fn from(raw: u32) -> Self {
        TextOffset(ShiftedU32::from(raw))
    }
}

impl std::ops::Add<usize> for TextOffset {
    type Output = TextOffset;

    fn add(self, rhs: usize) -> Self::Output {
        TextOffset(self.0 + rhs)
    }
}

impl std::ops::AddAssign<usize> for TextOffset {
    fn add_assign(&mut self, rhs: usize) {
        self.0 += rhs;
    }
}

impl std::ops::Sub<Self> for TextOffset {
    type Output = usize;

    fn sub(self, rhs: Self) -> Self::Output {
        self.index() - rhs.index()
    }
}

/// # Offset Range

#[derive(
    Debug, PartialEq, Default, Eq, PartialOrd, Ord, Clone, Copy, Hash, Serialize, Deserialize,
)]
pub struct TextOffsetRange {
    start: TextOffset,
    end: TextOffset,
}

impl From<Range<usize>> for TextOffsetRange {
    fn from(range: Range<usize>) -> Self {
        Self {
            start: TextOffset::from(range.start),
            end: TextOffset::from(range.end),
        }
    }
}

impl From<Range<TextOffset>> for TextOffsetRange {
    fn from(range: Range<TextOffset>) -> Self {
        Self {
            start: range.start,
            end: range.end,
        }
    }
}

impl Into<Range<usize>> for TextOffsetRange {
    fn into(self) -> Range<usize> {
        self.raw_range()
    }
}

impl TextOffsetRange {
    pub fn new(start: TextOffset, end: TextOffset) -> Self {
        Self { start, end }
    }

    pub fn raw_range(self) -> Range<usize> {
        self.start.index()..self.end.index()
    }

    pub fn raw_tuple(self) -> (usize, usize) {
        (self.start.index(), self.end.index())
    }

    pub fn join(self, other: Self) -> Self {
        Self {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }
}

impl TextOffsetRange {
    pub fn start(self) -> TextOffset {
        self.start
    }

    pub fn end(self) -> TextOffset {
        self.end
    }

    pub fn is_empty(self) -> bool {
        self.start == self.end
    }
}

impl std::ops::Index<TextOffsetRange> for str {
    type Output = str;

    fn index(&self, range: TextOffsetRange) -> &Self::Output {
        &self[range.start.index()..range.end.index()]
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, Serialize, Deserialize)]
#[serde(transparent)]
pub struct TextOffsetRangeFrom {
    start: TextOffset,
}

impl From<RangeFrom<TextOffset>> for TextOffsetRangeFrom {
    fn from(range: RangeFrom<TextOffset>) -> Self {
        Self { start: range.start }
    }
}

impl std::ops::Index<TextOffsetRangeFrom> for str {
    type Output = str;

    fn index(&self, range: TextOffsetRangeFrom) -> &Self::Output {
        &self[range.start.index()..]
    }
}

#[derive(
    Debug, PartialEq, Default, Eq, PartialOrd, Ord, Clone, Copy, Hash, Serialize, Deserialize,
)]
#[serde(transparent)]
pub struct TextOffsetRangeTo {
    end: TextOffset,
}

impl From<RangeTo<TextOffset>> for TextOffsetRangeTo {
    fn from(range: RangeTo<TextOffset>) -> Self {
        Self { end: range.end }
    }
}

impl TextOffsetRangeTo {
    pub fn end(self) -> TextOffset {
        self.end
    }

    pub fn raw(self) -> RangeTo<usize> {
        ..self.end.index()
    }
}

impl std::ops::Index<TextOffsetRangeTo> for str {
    type Output = str;

    fn index(&self, range: TextOffsetRangeTo) -> &Self::Output {
        &self[range.raw()]
    }
}
