use crate::*;
use std::num::NonZeroU32;

pub struct ArenaIdx<T> {
    raw: NonZeroU32,
    phantom: PhantomData<T>,
}

#[test]
fn option_arena_idx_size_works() {
    assert_eq!(
        std::mem::size_of::<Option<ArenaIdx<i32>>>(),
        std::mem::size_of::<u32>()
    )
}

impl<T> ArenaIdx<T> {
    pub(crate) fn new(index: usize) -> Self {
        Self {
            raw: unsafe { NonZeroU32::new_unchecked(index as u32 + 1) },
            phantom: PhantomData,
        }
    }

    pub unsafe fn from_raw(raw: usize) -> Self {
        Self::new(raw)
    }
    pub fn is(self, raw: usize) -> bool {
        self.index() == raw
    }

    pub fn index(self) -> usize {
        self.raw.get() as usize - 1
    }
}

impl<T> PartialEq for ArenaIdx<T> {
    fn eq(&self, other: &Self) -> bool {
        self.raw == other.raw
    }
}

impl<T> Eq for ArenaIdx<T> {}

impl<T> Clone for ArenaIdx<T> {
    fn clone(&self) -> Self {
        Self {
            raw: self.raw.clone(),
            phantom: PhantomData,
        }
    }
}

impl<T> Copy for ArenaIdx<T> {}

impl<T> PartialOrd for ArenaIdx<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.raw.partial_cmp(&other.raw)
    }
}

impl<T> Ord for ArenaIdx<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.raw.cmp(&other.raw)
    }
}

impl<T> std::hash::Hash for ArenaIdx<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.raw.hash(state);
    }
}

impl<T> Add<usize> for ArenaIdx<T> {
    type Output = Self;

    fn add(self, rhs: usize) -> Self::Output {
        Self::new(self.index() + rhs)
    }
}

impl<T> Sub<Self> for ArenaIdx<T> {
    type Output = usize;

    fn sub(self, rhs: Self) -> Self::Output {
        self.index() - rhs.index()
    }
}

impl<T> std::ops::Sub<usize> for ArenaIdx<T> {
    type Output = Self;

    fn sub(self, rhs: usize) -> Self::Output {
        Self::new(self.index() - rhs)
    }
}

impl<T> Debug for ArenaIdx<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.raw.fmt(f)
    }
}

impl<T, Db: ?Sized> salsa::DebugWithDb<Db> for ArenaIdx<T> {
    fn fmt(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        _db: &Db,
        _level: salsa::DebugFormatLevel,
    ) -> std::fmt::Result {
        Debug::fmt(&self.raw, f)
    }
}

impl<T> std::fmt::Display for ArenaIdx<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.raw)
    }
}

impl<T> Step for ArenaIdx<T> {
    fn steps_between(start: &Self, end: &Self) -> Option<usize> {
        if start.index() <= end.index() {
            Some(end.index() - start.index())
        } else {
            None
        }
    }

    fn forward_checked(start: Self, count: usize) -> Option<Self> {
        Some(start + count)
    }

    fn backward_checked(start: Self, count: usize) -> Option<Self> {
        if start.index() >= count {
            Some(start - count)
        } else {
            None
        }
    }
}