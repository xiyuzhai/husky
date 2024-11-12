use crate::*;
use husky_check_utils::should;

pub struct ArenaMap<T, V> {
    data: Vec<Option<V>>,
    phantom: PhantomData<T>,
}

impl<T, V> salsa::DebugWithDb for ArenaMap<T, V>
where
    T: salsa::DebugWithDb,
    V: salsa::DebugWithDb,
{
    fn debug_fmt_with_db(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        db: &::salsa::Db,
    ) -> std::fmt::Result {
        let elements = self
            .data
            .iter()
            .filter_map(|v| Some(v.as_ref()?.debug_with(db)));
        f.debug_list().entries(elements).finish()
    }
}

impl<T, V> PartialEq for ArenaMap<T, V>
where
    V: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data
    }
}

impl<T, V> Eq for ArenaMap<T, V> where V: Eq {}

impl<T, V> std::fmt::Debug for ArenaMap<T, V>
where
    V: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ArenaMap")
            .field("data", &self.data)
            .finish()
    }
}

impl<T, V> ArenaMap<T, V> {
    pub fn new(arena: &Arena<T>) -> Self {
        Self {
            data: arena.data().iter().map(|_| None).collect(),
            phantom: PhantomData,
        }
    }

    pub fn new_initialized(arena: &Arena<T>, f: impl Fn(ArenaIdx<T>, &T) -> Option<V>) -> Self {
        Self {
            data: arena.indexed_iter().map(|(idx, t)| f(idx, t)).collect(),
            phantom: PhantomData,
        }
    }

    pub fn new2(arena: ArenaRef<T>) -> Self {
        Self {
            data: arena.data().iter().map(|_| None).collect(),
            phantom: PhantomData,
        }
    }

    pub fn clone_for_extended(&self, extended_arena: &Arena<T>) -> Self
    where
        V: Clone,
    {
        assert!(self.data.len() <= extended_arena.len());
        let mut data = self.data.clone();
        data.reserve(extended_arena.len());
        for _ in self.data.len()..extended_arena.len() {
            data.push(None)
        }
        Self {
            data,
            phantom: PhantomData,
        }
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn has(&self, idx: ArenaIdx<T>) -> bool {
        self.data[idx.index()].is_some()
    }

    #[track_caller]
    pub fn get(&self, idx: ArenaIdx<T>) -> Option<&V> {
        match self.data[idx.index()] {
            Some(ref v) => Some(v),
            None => None,
        }
    }

    pub fn get_idx_by_value(&self, v: &V) -> Option<ArenaIdx<T>>
    where
        V: PartialEq,
    {
        self.data
            .iter()
            .position(|v1| match v1 {
                Some(v1) => v1 == v,
                None => false,
            })
            .map(ArenaIdx::new)
    }

    pub fn iter(&self) -> impl Iterator<Item = (ArenaIdx<T>, &V)> {
        self.data.iter().enumerate().filter_map(|(i, v)| match v {
            Some(ref v) => Some((ArenaIdx::new(i), v)),
            None => None,
        })
    }

    pub fn value_iter(&self) -> impl Iterator<Item = &V> {
        self.data.iter().filter_map(Option::as_ref)
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut V> {
        self.data.iter_mut().filter_map(|v| match v {
            Some(v) => Some(v),
            None => None,
        })
    }

    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.data.iter().filter_map(|v| v.as_ref())
    }

    pub fn insert(&mut self, idx: ArenaIdx<T>, v: V) -> Option<V> {
        std::mem::replace(&mut self.data[idx.index()], Some(v))
    }

    #[track_caller]
    pub fn insert_new(&mut self, idx: ArenaIdx<T>, v: V) {
        should!(self.data[idx.index()].is_none());
        self.data[idx.index()] = Some(v)
    }

    #[track_caller]
    pub fn insert_new_or_merge(&mut self, idx: ArenaIdx<T>, v: V, f: impl FnOnce(&mut V, V)) {
        match &mut self.data[idx.index()] {
            Some(v0) => f(v0, v),
            entry => *entry = Some(v),
        }
    }

    pub fn map<R>(&self, f: impl Fn(&V) -> R) -> ArenaMap<T, R> {
        ArenaMap {
            data: self
                .data
                .iter()
                .map(|v| match v.as_ref() {
                    Some(v) => Some(f(v)),
                    None => None,
                })
                .collect(),
            phantom: PhantomData,
        }
    }
}

impl<T, V> std::ops::Index<ArenaIdx<T>> for ArenaMap<T, V> {
    type Output = V;

    fn index(&self, index: ArenaIdx<T>) -> &Self::Output {
        self.get(index).unwrap()
    }
}

impl<T, V> std::ops::Index<&ArenaIdx<T>> for ArenaMap<T, V> {
    type Output = V;

    fn index(&self, index: &ArenaIdx<T>) -> &Self::Output {
        self.get(*index).unwrap()
    }
}

impl<T, V> std::ops::IndexMut<ArenaIdx<T>> for ArenaMap<T, V> {
    fn index_mut(&mut self, index: ArenaIdx<T>) -> &mut Self::Output {
        self.data[index.index()].as_mut().unwrap()
    }
}
