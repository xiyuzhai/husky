use std::fmt::Debug;

use super::*;
use shifted_unsigned_int::ShiftedU32;

#[derive(Clone, Copy)]
pub struct AnySeq(
    ShiftedU32,
    fn(ShiftedU32, &mut std::fmt::Formatter<'_>) -> std::fmt::Result,
);

impl std::fmt::Debug for AnySeq {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        (self.1)(self.0, f)
    }
}

impl<T> From<Seq<T>> for AnySeq
where
    T: std::fmt::Debug + Any + Send + Sync,
{
    fn from(seq: Seq<T>) -> Self {
        Self(seq.0, |index, f| {
            let seq = Seq::<T>(index, PhantomData);
            seq.fmt(f)
        })
    }
}
