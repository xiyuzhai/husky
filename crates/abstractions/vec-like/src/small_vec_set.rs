use crate::{error::InsertEntryRepeatError, *};
use smallvec::*;

#[derive(Debug, PartialEq, Eq, Clone, Hash, Serialize, Deserialize)]
pub struct SmallVecSet<K, const N: usize>
where
    [K; N]: Array<Item = K>,
{
    data: SmallVec<[K; N]>,
}

impl<K, const N: usize> SmallVecSet<K, N>
where
    [K; N]: Array<Item = K>,
{
    pub fn new_one_elem_set(elem: K) -> Self {
        Self {
            data: smallvec![elem],
        }
    }
}

impl<K, const N: usize> Default for SmallVecSet<K, N>
where
    [K; N]: Array<Item = K>,
{
    fn default() -> Self {
        Self {
            data: Default::default(),
        }
    }
}

impl<K, const N: usize> Deref for SmallVecSet<K, N>
where
    K: PartialEq + Eq + Copy,
    [K; N]: Array<Item = K>,
{
    type Target = [K];

    fn deref(&self) -> &Self::Target {
        &self.data
    }
}
impl<K, const N: usize> AsRef<[K]> for SmallVecSet<K, N>
where
    [K; N]: Array<Item = K>,
{
    fn as_ref(&self) -> &[K] {
        &self.data
    }
}

impl<K, const N: usize> FromIterator<K> for SmallVecSet<K, N>
where
    [K; N]: Array<Item = K>,
    K: Copy + Eq,
{
    fn from_iter<T: IntoIterator<Item = K>>(t: T) -> Self {
        let mut slf = Self {
            data: Default::default(),
        };
        for elem in t {
            slf.insert(elem)
        }
        slf
    }
}

impl<K, const N: usize> IntoIterator for &SmallVecSet<K, N>
where
    [K; N]: Array<Item = K>,
    K: Copy + Eq,
{
    type Item = K;

    type IntoIter = impl Iterator<Item = K>;

    fn into_iter(self) -> Self::IntoIter {
        self.data.iter().copied()
    }
}

impl<K, const N: usize, const N2: usize> From<[K; N2]> for SmallVecSet<K, N>
where
    [K; N]: Array<Item = K>,
    K: Copy + Eq,
{
    fn from(value: [K; N2]) -> Self {
        Self::from_iter(value.into_iter())
    }
}

impl<'a, K, const N: usize> From<&'a [K]> for SmallVecSet<K, N>
where
    K: Copy + Eq,
{
    fn from(value: &'a [K]) -> Self {
        Self::from_iter(value.iter().copied())
    }
}

impl<K, const N: usize> SmallVecSet<K, N>
where
    [K; N]: Array<Item = K>,
{
    pub fn len(&self) -> usize {
        self.data.len()
    }
    pub fn has(&self, key: K) -> bool
    where
        K: Copy + PartialEq + Eq,
    {
        self.data.iter().find(|entry| **entry == key).is_some()
    }
    pub fn has_ref(&self, key: &K) -> bool
    where
        K: PartialEq + Eq,
    {
        self.data.iter().find(|entry| *entry == key).is_some()
    }

    pub fn contains(&self, key: &K) -> bool
    where
        K: PartialEq + Eq,
    {
        self.data.iter().find(|entry| *entry == key).is_some()
    }

    pub fn insert_new(&mut self, new: K) -> Result<(), InsertEntryRepeatError<K>>
    where
        K: Copy + PartialEq + Eq,
    {
        if self.has(new) {
            Err(InsertEntryRepeatError {
                old: self
                    .data
                    .iter()
                    .position(|entry| *entry == new)
                    .unwrap()
                    .into(),
                new,
            })
        } else {
            self.data.push(new);
            Ok(())
        }
    }

    pub fn clear(&mut self) {
        self.data.clear()
    }

    pub fn toggle(&mut self, value: K)
    where
        K: PartialEq + Eq,
    {
        if let Some(position) = self.data.iter().position(|entry| *entry == value) {
            self.data.remove(position);
        } else {
            self.data.push(value)
        }
    }

    pub fn to_vec(&self) -> SmallVec<[K; N]>
    where
        K: Copy,
    {
        self.data.clone()
    }

    pub fn insert(&mut self, value: K)
    where
        K: Copy + PartialEq + Eq,
    {
        if self.has(value) {
            ()
        } else {
            self.data.push(value)
        }
    }

    pub fn insert_move(&mut self, value: K)
    where
        K: Copy + PartialEq + Eq,
    {
        if self.contains(&value) {
            ()
        } else {
            self.data.push(value)
        }
    }

    pub fn extend(&mut self, other: impl IntoIterator<Item = K>)
    where
        K: Copy + PartialEq + Eq,
    {
        for entry in other {
            self.insert(entry)
        }
    }

    pub fn data(&self) -> &[K] {
        self.data.as_ref()
    }
}
