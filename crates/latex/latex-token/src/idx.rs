use shifted_unsigned_int::ShiftedU32;
use std::iter::Step;
use std::ops::{Add, Sub};

use crate::lane::LxTokenLane;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct LxTokenIdx(LxTokenLane, ShiftedU32);

impl LxTokenIdx {
    pub(crate) fn lane(self) -> LxTokenLane {
        self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LxMathTokenIdx(pub(crate) LxTokenIdx);

impl std::ops::Add<usize> for LxMathTokenIdx {
    type Output = Self;
    fn add(self, rhs: usize) -> Self::Output {
        Self(self.0 + rhs)
    }
}

impl std::ops::Deref for LxMathTokenIdx {
    type Target = LxTokenIdx;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl std::convert::AsRef<LxTokenIdx> for LxMathTokenIdx {
    fn as_ref(&self) -> &LxTokenIdx {
        &self.0
    }
}

impl std::borrow::Borrow<LxTokenIdx> for LxMathTokenIdx {
    fn borrow(&self) -> &LxTokenIdx {
        &self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LxRootTokenIdx(pub(crate) LxTokenIdx);

impl std::ops::Deref for LxRootTokenIdx {
    type Target = LxTokenIdx;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl std::convert::AsRef<LxTokenIdx> for LxRootTokenIdx {
    fn as_ref(&self) -> &LxTokenIdx {
        &self.0
    }
}

impl std::borrow::Borrow<LxTokenIdx> for LxRootTokenIdx {
    fn borrow(&self) -> &LxTokenIdx {
        &self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LxSpecTokenIdx(pub(crate) LxTokenIdx);

impl std::ops::Deref for LxSpecTokenIdx {
    type Target = LxTokenIdx;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl std::convert::AsRef<LxTokenIdx> for LxSpecTokenIdx {
    fn as_ref(&self) -> &LxTokenIdx {
        &self.0
    }
}

impl std::borrow::Borrow<LxTokenIdx> for LxSpecTokenIdx {
    fn borrow(&self) -> &LxTokenIdx {
        &self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LxRoseTokenIdx(pub(crate) LxTokenIdx);

impl std::ops::Deref for LxRoseTokenIdx {
    type Target = LxTokenIdx;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl std::convert::AsRef<LxTokenIdx> for LxRoseTokenIdx {
    fn as_ref(&self) -> &LxTokenIdx {
        &self.0
    }
}

impl std::borrow::Borrow<LxTokenIdx> for LxRoseTokenIdx {
    fn borrow(&self) -> &LxTokenIdx {
        &self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LxNameTokenIdx(pub(crate) LxTokenIdx);

impl std::ops::Deref for LxNameTokenIdx {
    type Target = LxTokenIdx;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl std::convert::AsRef<LxTokenIdx> for LxNameTokenIdx {
    fn as_ref(&self) -> &LxTokenIdx {
        &self.0
    }
}

impl std::borrow::Borrow<LxTokenIdx> for LxNameTokenIdx {
    fn borrow(&self) -> &LxTokenIdx {
        &self.0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LxLispTokenIdx(pub(crate) LxTokenIdx);

impl std::ops::Deref for LxLispTokenIdx {
    type Target = LxTokenIdx;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl std::convert::AsRef<LxTokenIdx> for LxLispTokenIdx {
    fn as_ref(&self) -> &LxTokenIdx {
        &self.0
    }
}

impl std::borrow::Borrow<LxTokenIdx> for LxLispTokenIdx {
    fn borrow(&self) -> &LxTokenIdx {
        &self.0
    }
}

impl LxTokenIdx {
    pub(crate) fn from_index(lane: LxTokenLane, index: usize) -> Self {
        Self(lane, index.into())
    }

    pub fn index(self) -> usize {
        self.1.index()
    }
}

impl Add<usize> for LxTokenIdx {
    type Output = Self;
    fn add(self, rhs: usize) -> Self::Output {
        Self(self.0, self.1 + rhs)
    }
}

impl Sub<usize> for LxTokenIdx {
    type Output = Self;
    fn sub(self, rhs: usize) -> Self::Output {
        Self(self.0, self.1 - rhs)
    }
}

impl Step for LxTokenIdx {
    fn steps_between(start: &Self, end: &Self) -> Option<usize> {
        end.1.index().checked_sub(start.1.index()).map(|diff| diff)
    }
    fn forward_checked(start: Self, count: usize) -> Option<Self> {
        start
            .1
            .checked_add(count.try_into().ok()?)
            .map(|idx| Self(start.0, idx))
    }
    fn backward_checked(start: Self, count: usize) -> Option<Self> {
        start
            .1
            .checked_sub(count.try_into().ok()?)
            .map(|idx| Self(start.0, idx))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LxTokenIdxRange {
    lane: LxTokenLane,
    start: ShiftedU32,
    end: ShiftedU32,
}

impl From<std::ops::Range<LxTokenIdx>> for LxTokenIdxRange {
    fn from(range: std::ops::Range<LxTokenIdx>) -> Self {
        Self {
            lane: range.start.0,
            start: range.start.1,
            end: range.end.1,
        }
    }
}

impl IntoIterator for LxTokenIdxRange {
    type Item = LxTokenIdx;
    type IntoIter = std::ops::Range<LxTokenIdx>;

    fn into_iter(self) -> Self::IntoIter {
        LxTokenIdx::from_index(self.lane, self.start.index())
            ..LxTokenIdx::from_index(self.lane, self.end.index())
    }
}

impl From<(LxTokenLane, std::ops::Range<usize>)> for LxTokenIdxRange {
    fn from((lane, range): (LxTokenLane, std::ops::Range<usize>)) -> Self {
        Self {
            lane,
            start: range.start.into(),
            end: range.end.into(),
        }
    }
}

impl LxTokenIdxRange {
    pub(crate) fn from_usize_range(lane: LxTokenLane, range: std::ops::Range<usize>) -> Self {
        Self {
            lane,
            start: range.start.into(),
            end: range.end.into(),
        }
    }

    pub fn new_single(idx: LxTokenIdx) -> Self {
        Self {
            lane: idx.0,
            start: idx.1,
            end: idx.1 + 1,
        }
    }

    pub fn new_closed(first: LxTokenIdx, last: LxTokenIdx) -> Self {
        Self {
            lane: first.0,
            start: first.1,
            end: last.1 + 1,
        }
    }

    pub fn new(start: LxTokenIdx, end: LxTokenIdx) -> Self {
        Self {
            lane: start.0,
            start: start.1,
            end: end.1,
        }
    }
}

impl LxTokenIdxRange {
    pub(crate) fn is_empty(self) -> bool {
        self.start == self.end
    }

    pub fn start(&self) -> LxTokenIdx {
        LxTokenIdx(self.lane, self.start)
    }

    pub fn end(&self) -> LxTokenIdx {
        LxTokenIdx(self.lane, self.end)
    }

    pub fn last(&self) -> Option<LxTokenIdx> {
        if self.is_empty() {
            None
        } else {
            Some(LxTokenIdx(self.lane, self.end - 1))
        }
    }

    pub fn join(self, other: Self) -> Self {
        Self {
            lane: self.lane,
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }

    pub fn to_included(self, last: LxTokenIdx) -> Self {
        Self {
            lane: self.lane,
            start: self.start,
            end: last.1 + 1,
        }
    }
}
