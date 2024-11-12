use super::*;

impl<T> Seq<Option<T>>
where
    T: Copy + Any + Send + Sync,
{
    pub fn or(self, other: Self) -> Self {
        Option::or.apply(self, other)
    }
}

impl<T> std::ops::BitOrAssign for Seq<Option<T>>
where
    T: Copy + Any + Send + Sync,
{
    fn bitor_assign(&mut self, rhs: Self) {
        *self = self.or(rhs)
    }
}
