use shifted_unsigned_int::ShiftedU32;
use std::iter::Step;
use std::ops::{Add, Sub};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct LxTokenIdx(ShiftedU32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct LxCodeTokenIdx(pub(crate) LxTokenIdx);

impl std::ops::Deref for LxCodeTokenIdx {
    type Target = LxTokenIdx;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl std::convert::AsRef<LxTokenIdx> for LxCodeTokenIdx {
    fn as_ref(&self) -> &LxTokenIdx {
        &self.0
    }
}

impl std::borrow::Borrow<LxTokenIdx> for LxCodeTokenIdx {
    fn borrow(&self) -> &LxTokenIdx {
        &self.0
    }
}

impl LxTokenIdx {
    pub(crate) fn from_index(index: usize) -> Self {
        Self(index.into())
    }

    pub fn index(self) -> usize {
        self.0.index()
    }
}

impl Add<usize> for LxTokenIdx {
    type Output = Self;
    fn add(self, rhs: usize) -> Self::Output {
        Self(self.0 + rhs)
    }
}

impl Sub<usize> for LxTokenIdx {
    type Output = Self;
    fn sub(self, rhs: usize) -> Self::Output {
        Self(self.0 - rhs)
    }
}

impl Step for LxTokenIdx {
    fn steps_between(start: &Self, end: &Self) -> Option<usize> {
        end.0.index().checked_sub(start.0.index()).map(|diff| diff)
    }
    fn forward_checked(start: Self, count: usize) -> Option<Self> {
        start.0.checked_add(count.try_into().ok()?).map(Self)
    }
    fn backward_checked(start: Self, count: usize) -> Option<Self> {
        start.0.checked_sub(count.try_into().ok()?).map(Self)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LxTokenIdxRange {
    start: ShiftedU32,
    end: ShiftedU32,
}

impl From<std::ops::Range<LxTokenIdx>> for LxTokenIdxRange {
    fn from(range: std::ops::Range<LxTokenIdx>) -> Self {
        Self {
            start: range.start.0,
            end: range.end.0,
        }
    }
}

impl IntoIterator for LxTokenIdxRange {
    type Item = LxTokenIdx;
    type IntoIter = std::ops::Range<LxTokenIdx>;

    fn into_iter(self) -> Self::IntoIter {
        LxTokenIdx::from_index(self.start.index())..LxTokenIdx::from_index(self.end.index())
    }
}

impl From<std::ops::Range<usize>> for LxTokenIdxRange {
    fn from(range: std::ops::Range<usize>) -> Self {
        Self {
            start: range.start.into(),
            end: range.end.into(),
        }
    }
}

impl LxTokenIdxRange {
    pub(crate) fn new(range: std::ops::Range<usize>) -> Self {
        Self {
            start: range.start.into(),
            end: range.end.into(),
        }
    }

    pub fn new_single(idx: LxTokenIdx) -> Self {
        Self {
            start: idx.0,
            end: (idx + 1).0,
        }
    }

    pub fn new_closed(first: LxTokenIdx, last: LxTokenIdx) -> Self {
        Self {
            start: first.0,
            end: last.0 + 1usize,
        }
    }
}

impl LxTokenIdxRange {
    pub(crate) fn is_empty(self) -> bool {
        self.start == self.end
    }

    pub fn start(&self) -> LxTokenIdx {
        LxTokenIdx(self.start)
    }

    pub fn last(&self) -> Option<LxTokenIdx> {
        if self.is_empty() {
            None
        } else {
            Some(LxTokenIdx(self.end - 1))
        }
    }

    pub fn join(self, other: Self) -> Self {
        Self {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }

    pub fn to_included(self, last: LxTokenIdx) -> Self {
        Self {
            start: self.start,
            end: last.0 + 1,
        }
    }
}
