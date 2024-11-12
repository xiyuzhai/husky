#![feature(impl_trait_in_assoc_type)]
#![feature(step_trait)]
mod arena;
mod arena_idx;
mod arena_ref;
pub mod map;
pub mod ordered_map;
#[cfg(test)]
mod tests;

pub use self::arena::*;
pub use self::arena_idx::*;
pub use self::arena_ref::*;

use std::{
    fmt::Debug,
    iter::Step,
    marker::PhantomData,
    ops::{Add, Sub},
};

pub struct ArenaIdxRange<T> {
    start: ArenaIdx<T>,
    end: ArenaIdx<T>,
}

impl<T> PartialOrd for ArenaIdxRange<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> Ord for ArenaIdxRange<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // First, compare the start indices
        match self.start.cmp(&other.start) {
            std::cmp::Ordering::Equal => {}
            ord => return ord,
        }
        // If starts are equal, compare the end indices
        self.end.cmp(&other.end)
    }
}

impl<T> ArenaIdxRange<T> {
    pub fn split_last(self) -> (Self, ArenaIdx<T>) {
        debug_assert!(self.start < self.end);
        let last = self.end - 1;
        (
            Self {
                start: self.start,
                end: last,
            },
            last,
        )
    }
}

impl<T> std::fmt::Debug for ArenaIdxRange<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("ArenaIdxRange")
            .field(&(self.start..self.end))
            .finish()
    }
}

impl<T> salsa::DebugWithDb for ArenaIdxRange<T> {
    fn debug_fmt_with_db(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        db: &salsa::Db,
    ) -> std::fmt::Result {
        self.fmt(f)
    }
}

impl<T> Clone for ArenaIdxRange<T> {
    fn clone(&self) -> Self {
        Self {
            start: self.start,
            end: self.end,
        }
    }
}

impl<T> Copy for ArenaIdxRange<T> {}

impl<T> PartialEq for ArenaIdxRange<T> {
    fn eq(&self, other: &Self) -> bool {
        self.start == other.start && self.end == other.end
    }
}

impl<T> Eq for ArenaIdxRange<T> {}

impl<T> std::hash::Hash for ArenaIdxRange<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.start.hash(state);
        self.end.hash(state);
    }
}

impl<T> IntoIterator for ArenaIdxRange<T> {
    type Item = ArenaIdx<T>;

    type IntoIter = impl Iterator<Item = Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.to_range()
    }
}

impl<T> IntoIterator for &ArenaIdxRange<T> {
    type Item = ArenaIdx<T>;

    type IntoIter = impl Iterator<Item = Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.to_range().clone().into_iter()
    }
}

impl<T> ArenaIdxRange<T> {
    pub fn to_range(&self) -> std::ops::Range<ArenaIdx<T>> {
        self.start..self.end
    }

    pub fn len(&self) -> usize {
        self.end.index() - self.start.index()
    }

    pub fn is_empty(&self) -> bool {
        self.start == self.end
    }

    pub fn start(&self) -> ArenaIdx<T> {
        self.start
    }

    pub fn end(&self) -> ArenaIdx<T> {
        self.end
    }

    pub fn contains(&self, idx: ArenaIdx<T>) -> bool {
        self.start <= idx && self.end > idx
    }

    pub fn first(&self) -> Option<ArenaIdx<T>> {
        if self.start < self.end {
            Some(self.start)
        } else {
            None
        }
    }

    pub fn last(&self) -> Option<ArenaIdx<T>> {
        if self.start < self.end {
            Some(self.end - 1)
        } else {
            None
        }
    }

    pub fn new_single(idx: ArenaIdx<T>) -> Self {
        Self {
            start: idx,
            end: idx + 1,
        }
    }

    pub unsafe fn new(start: ArenaIdx<T>, end: ArenaIdx<T>) -> Self {
        Self { start, end }
    }
}
