use super::*;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Idx(ShiftedU32);

impl std::fmt::Debug for Idx {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("#{}", self.0.index()))
    }
}

impl Idx {
    pub fn new(i: usize) -> Self {
        Self(i.into())
    }
}

impl Idx {
    pub fn index(self) -> usize {
        self.0.index()
    }
}

#[macro_export]
macro_rules! idx {
    ($i: expr) => {
        $crate::seq::idx::Idx::new($i)
    };
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct IdxRange {
    start: Idx,
    end: Idx,
}

impl std::fmt::Debug for IdxRange {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("{:?}..{:?}", self.start, self.end))
    }
}

impl IdxRange {
    pub fn new(start: Idx, end: Idx) -> Self {
        Self { start, end }
    }
}

impl IdxRange {
    pub fn start(&self) -> Idx {
        self.start
    }

    pub fn end(&self) -> Idx {
        self.end
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Option2<T> {
    first: Option<T>,
    second: Option<T>,
}

impl<T> Option2<T> {
    pub fn first(self) -> Option<T> {
        self.first
    }

    pub fn second(self) -> Option<T> {
        self.second
    }
}

impl<T> FromIterator<T> for Option2<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut iter = iter.into_iter();
        let first = iter.next();
        let second = iter.next();
        Self { first, second }
    }
}

impl<T> Seq<Option<T>>
where
    T: Any + Send + Sync + Copy,
{
    pub fn nearest_left(self) -> Seq<Option<(Idx, T)>> {
        let ts = self.data();
        Seq::new(
            (0..ts.len())
                .map(|i| nearest_left_at_index(ts, i))
                .collect(),
        )
    }

    pub fn nearest_left2(self) -> Seq<Option2<(Idx, T)>> {
        let ts = self.data();
        Seq::new(
            (0..ts.len())
                .map(|i| nearest_left2_at_index(ts, i))
                .collect(),
        )
    }

    pub fn nearest_right(self) -> Seq<Option<(Idx, T)>> {
        let ts = self.data();
        Seq::new(
            (0..ts.len())
                .map(|i| nearest_right_at_index(ts, i))
                .collect(),
        )
    }

    pub fn nearest_right2(self) -> Seq<Option2<(Idx, T)>> {
        let ts = self.data();
        Seq::new(
            (0..ts.len())
                .map(|i| nearest_right2_at_index(ts, i))
                .collect(),
        )
    }
}

fn nearest_left_at_index<T>(ts: &[Option<T>], i: usize) -> Option<(Idx, T)>
where
    T: Any + Send + Sync + Copy,
{
    (1..=i)
        .into_iter()
        .filter_map(|j| ts[i - j].map(|t| (idx!(i - j), t)))
        .next()
}

fn nearest_left2_at_index<T>(ts: &[Option<T>], i: usize) -> Option2<(Idx, T)>
where
    T: Any + Send + Sync + Copy,
{
    (1..=i)
        .into_iter()
        .filter_map(|j| ts[i - j].map(|t| (idx!(i - j), t)))
        .collect()
}

fn nearest_right_at_index<T>(ts: &[Option<T>], i: usize) -> Option<(Idx, T)>
where
    T: Any + Send + Sync + Copy,
{
    ((i + 1)..ts.len())
        .into_iter()
        .filter_map(|j| ts[j].map(|t| (idx!(j), t)))
        .next()
}

fn nearest_right2_at_index<T>(ts: &[Option<T>], i: usize) -> Option2<(Idx, T)>
where
    T: Any + Send + Sync + Copy,
{
    ((i + 1)..ts.len())
        .into_iter()
        .filter_map(|j| ts[j].map(|t| (idx!(j), t)))
        .collect()
}

#[test]
fn seq_nearest_left_works() {
    fn t<T>(ts: Seq<Option<T>>, expect: &[Option<(Idx, T)>])
    where
        T: Any + Send + Sync + Copy + Eq + std::fmt::Debug,
    {
        assert_eq!(ts.nearest_left().data(), expect);
    }
    t::<i32>(seq![], &[]);
    t::<i32>(seq![None], &[None]);
    t::<i32>(seq![None, Some(1)], &[None, None]);
    t::<i32>(seq![Some(1), None], &[None, Some((idx!(0), 1))]);
    t(
        seq![None, Some(1), Some(2), Some(3), Some(4), None],
        &[
            None,
            None,
            Some((idx!(1), 1)),
            Some((idx!(2), 2)),
            Some((idx!(3), 3)),
            Some((idx!(4), 4)),
        ],
    );
}

#[test]
fn seq_nearest_right_works() {
    fn t<T>(ts: Seq<Option<T>>, expect: &[Option<(Idx, T)>])
    where
        T: Any + Send + Sync + Copy + Eq + std::fmt::Debug,
    {
        assert_eq!(ts.nearest_right().data(), expect);
    }
    t::<i32>(seq![], &[]);
    t::<i32>(seq![None], &[None]);
    t::<i32>(seq![None, Some(1)], &[Some((idx!(1), 1)), None]);
    t::<i32>(seq![Some(1), None], &[None, None]);
    t(
        seq![None, Some(1), Some(2), Some(3), Some(4), None],
        &[
            Some((idx!(1), 1)),
            Some((idx!(2), 2)),
            Some((idx!(3), 3)),
            Some((idx!(4), 4)),
            None,
            None,
        ],
    );
}
