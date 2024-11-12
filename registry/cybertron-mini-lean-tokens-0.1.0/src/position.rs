use shifted_unsigned_int::ShiftedU32;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PositionIdx(ShiftedU32);

impl PositionIdx {
    pub(crate) fn new(position: u32) -> Self {
        Self(todo!())
    }
}

impl Into<u32> for PositionIdx {
    fn into(self) -> u32 {
        self.0.into()
    }
}
