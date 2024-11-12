use serde::{Deserialize, Serialize};
use shifted_unsigned_int::ShiftedU32;

/// Character byte offset on a line in a document (zero-based). The meaning of this
/// offset is determined by the negotiated `PositionEncodingKind`.
///
/// If the character value is greater than the line length it defaults back
/// to the line length.
#[derive(
    Debug, PartialEq, Default, Eq, PartialOrd, Ord, Clone, Copy, Hash, Serialize, Deserialize,
)]
#[serde(transparent)]
pub struct TextColumn(ShiftedU32);

impl std::ops::Add<u32> for TextColumn {
    type Output = Self;
    fn add(self, rhs: u32) -> Self::Output {
        TextColumn(self.0 + rhs)
    }
}

impl std::ops::Sub<u32> for TextColumn {
    type Output = Self;
    fn sub(self, rhs: u32) -> Self::Output {
        TextColumn(self.0 - rhs)
    }
}

impl std::ops::AddAssign<u32> for TextColumn {
    fn add_assign(&mut self, rhs: u32) {
        self.0 += rhs;
    }
}

impl std::ops::SubAssign<u32> for TextColumn {
    fn sub_assign(&mut self, rhs: u32) {
        self.0 -= rhs;
    }
}

impl TextColumn {
    pub fn index(&self) -> usize {
        self.0.index()
    }

    pub fn index32(&self) -> u32 {
        self.0.into()
    }
}

impl From<u32> for TextColumn {
    fn from(raw: u32) -> Self {
        TextColumn(ShiftedU32::from(raw))
    }
}

impl From<usize> for TextColumn {
    fn from(raw: usize) -> Self {
        TextColumn(ShiftedU32::from(raw))
    }
}

impl From<i32> for TextColumn {
    fn from(raw: i32) -> Self {
        assert!(raw >= 0);
        let raw: u32 = raw.try_into().unwrap();
        TextColumn(ShiftedU32::from(raw))
    }
}

#[test]
fn test_conversion() {
    let a: i32 = -1;
    let _b: u32 = a as u32;
}
