use crate::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Arena<T> {
    data: Vec<T>,
}

impl<'a, T> IntoIterator for &'a Arena<T> {
    type Item = &'a T;

    type IntoIter = impl Iterator<Item = &'a T> + 'a;

    fn into_iter(self) -> Self::IntoIter {
        self.data.iter()
    }
}

impl<T> Default for Arena<T> {
    fn default() -> Self {
        Self {
            data: Default::default(),
        }
    }
}

impl<T> salsa::DebugWithDb for Arena<T>
where
    T: salsa::DebugWithDb,
{
    fn debug_fmt_with_db(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        db: &::salsa::Db,
    ) -> std::fmt::Result {
        f.debug_struct("Arena")
            .field("data", &self.data.debug_with(db))
            .finish()
    }
}

impl<T> Arena<T> {
    pub unsafe fn new_ext(data: Vec<T>) -> Self {
        Self { data }
    }
}

impl<T> Arena<T> {
    #[inline]
    pub fn alloc_batch(&mut self, items: impl IntoIterator<Item = T>) -> ArenaIdxRange<T> {
        let start = ArenaIdx::new(self.data.len());
        self.data.extend(items);
        let end = ArenaIdx::new(self.data.len());
        ArenaIdxRange { start, end }
    }

    pub fn alloc_one(&mut self, item: T) -> ArenaIdx<T> {
        let idx = ArenaIdx::new(self.data.len());
        self.data.push(item);
        idx
    }

    pub unsafe fn next_idx(&self) -> ArenaIdx<T> {
        ArenaIdx::new(self.data.len())
    }

    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.data.len()
    }

    #[inline]
    pub fn data(&self) -> &[T] {
        &self.data
    }

    #[inline]
    pub fn set(&mut self, idx: ArenaIdx<T>, new_value: T) {
        self.data[idx.index()] = new_value
    }

    #[inline]
    pub fn update(&mut self, idx: ArenaIdx<T>, f: impl FnOnce(&mut T)) {
        f(&mut self.data[idx.index()])
    }

    #[inline]
    pub fn iter<'a>(&'a self) -> impl Iterator<Item = &'a T> + 'a {
        self.data.iter()
    }

    pub fn iter_mut<'a>(&'a mut self) -> impl Iterator<Item = &'a mut T> + 'a {
        self.data.iter_mut()
    }

    pub fn iter_mut_with_start<'a>(
        &'a mut self,
        start: usize,
    ) -> impl Iterator<Item = &'a mut T> + 'a {
        self.data[start..].iter_mut()
    }

    pub fn indices<'a>(&'a self) -> impl Iterator<Item = ArenaIdx<T>> {
        (0..self.data.len()).map(|i| ArenaIdx::new(i))
    }

    pub fn indexed_iter<'a>(&'a self) -> impl Iterator<Item = (ArenaIdx<T>, &'a T)> + 'a {
        self.data
            .iter()
            .enumerate()
            .map(|(i, t)| (ArenaIdx::new(i), t))
    }

    pub fn indexed_copy_iter<'a>(&'a self) -> impl Iterator<Item = (ArenaIdx<T>, T)> + 'a
    where
        T: Copy,
    {
        self.data
            .iter()
            .copied()
            .enumerate()
            .map(|(i, t)| (ArenaIdx::new(i), t))
    }

    pub fn indexed_iter_with_start<'a>(
        &'a self,
        start: usize,
    ) -> impl Iterator<Item = (ArenaIdx<T>, &'a T)> + 'a {
        self.data[start..]
            .iter()
            .enumerate()
            .map(move |(i, t)| (ArenaIdx::new(start + i), t))
    }

    pub fn indexed_iter_mut_with_start<'a>(
        &'a mut self,
        start: usize,
    ) -> impl Iterator<Item = (ArenaIdx<T>, &'a mut T)> + 'a {
        self.data[start..]
            .iter_mut()
            .enumerate()
            .map(move |(i, t)| (ArenaIdx::new(start + i), t))
    }

    pub fn find_rev_indexed(&self, f: impl Fn(&T) -> bool) -> Option<(ArenaIdx<T>, &T)> {
        self.data.iter().rev().position(|t| f(t)).map(|raw_rev| {
            let raw = self.data.len() - raw_rev - 1;
            (ArenaIdx::new(raw), &self.data[raw])
        })
    }
}

impl<T> FromIterator<T> for Arena<T> {
    fn from_iter<Iter: IntoIterator<Item = T>>(iter: Iter) -> Self {
        Self {
            data: iter.into_iter().collect(),
        }
    }
}

impl<T> core::ops::Index<ArenaIdx<T>> for Arena<T> {
    type Output = T;

    fn index(&self, idx: ArenaIdx<T>) -> &Self::Output {
        &self.data[idx.index()]
    }
}

impl<T> core::ops::Index<&ArenaIdx<T>> for Arena<T> {
    type Output = T;

    fn index(&self, idx: &ArenaIdx<T>) -> &Self::Output {
        &self.data[idx.index()]
    }
}

impl<T> core::ops::Index<ArenaIdxRange<T>> for Arena<T> {
    type Output = [T];

    fn index(&self, idx: ArenaIdxRange<T>) -> &Self::Output {
        &self.data[idx.start.index()..idx.end.index()]
    }
}

impl<T> core::ops::Index<&ArenaIdxRange<T>> for Arena<T> {
    type Output = [T];

    fn index(&self, idx: &ArenaIdxRange<T>) -> &Self::Output {
        &self.data[idx.start.index()..idx.end.index()]
    }
}
