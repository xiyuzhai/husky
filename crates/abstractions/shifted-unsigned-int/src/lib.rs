#![feature(nonzero_ops)]
use std::{
    num::{NonZeroU16, NonZeroU32, NonZeroU64, NonZeroU8, NonZeroUsize},
    ops::{Add, AddAssign, Sub, SubAssign},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(from = "usize", into = "usize"))]
pub struct ShiftedU8(NonZeroU8);

impl Default for ShiftedU8 {
    fn default() -> Self {
        0usize.into()
    }
}

impl From<usize> for ShiftedU8 {
    fn from(value: usize) -> Self {
        debug_assert!(value + 1 < u8::MAX as usize);
        ShiftedU8(unsafe { NonZeroU8::new_unchecked((value + 1) as u8) })
    }
}

impl Into<usize> for ShiftedU8 {
    fn into(self) -> usize {
        self.0.get() as usize - 1
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(from = "usize", into = "usize"))]
pub struct ShiftedU16(NonZeroU16);

impl Default for ShiftedU16 {
    fn default() -> Self {
        0usize.into()
    }
}

impl From<usize> for ShiftedU16 {
    fn from(value: usize) -> Self {
        debug_assert!(value + 1 < u16::MAX as usize);
        ShiftedU16(unsafe { NonZeroU16::new_unchecked((value + 1) as u16) })
    }
}

impl Into<usize> for ShiftedU16 {
    fn into(self) -> usize {
        self.0.get() as usize - 1
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(from = "usize", into = "usize"))]
pub struct ShiftedU32(NonZeroU32);

impl std::fmt::Debug for ShiftedU32 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.index().fmt(f)
    }
}

impl Default for ShiftedU32 {
    fn default() -> Self {
        0usize.into()
    }
}

impl ShiftedU32 {
    pub fn new(value: u32) -> Self {
        ShiftedU32(unsafe { NonZeroU32::new_unchecked(value + 1) })
    }

    pub unsafe fn unchecked_add(self, rhs: u32) -> Self {
        Self(self.0.unchecked_add(rhs))
    }

    pub fn checked_add(&self, count: u32) -> Option<Self> {
        self.0.checked_add(count).map(Self)
    }

    pub fn checked_sub(&self, count: u32) -> Option<Self> {
        let raw = self.0.get().checked_sub(count)?;
        Some(Self(raw.try_into().ok()?))
    }
}

impl From<i32> for ShiftedU32 {
    fn from(value: i32) -> Self {
        let value: u32 = value.try_into().unwrap();
        ShiftedU32::from(value)
    }
}

impl From<u32> for ShiftedU32 {
    fn from(value: u32) -> Self {
        debug_assert!(value + 1 < u32::MAX as u32);
        ShiftedU32(unsafe { NonZeroU32::new_unchecked((value + 1) as u32) })
    }
}

impl From<usize> for ShiftedU32 {
    fn from(value: usize) -> Self {
        debug_assert!(value + 1 < u32::MAX as usize);
        ShiftedU32(unsafe { NonZeroU32::new_unchecked((value + 1) as u32) })
    }
}

impl Into<u32> for ShiftedU32 {
    fn into(self) -> u32 {
        self.0.get() - 1
    }
}

impl Into<usize> for ShiftedU32 {
    fn into(self) -> usize {
        self.index()
    }
}

impl ShiftedU32 {
    pub fn index(self) -> usize {
        self.0.get() as usize - 1
    }
}

impl Add<u32> for ShiftedU32 {
    type Output = Self;

    fn add(self, rhs: u32) -> Self::Output {
        ShiftedU32(unsafe { NonZeroU32::new_unchecked(self.0.get() + rhs) })
    }
}

impl Add<i32> for ShiftedU32 {
    type Output = Self;

    fn add(self, rhs: i32) -> Self::Output {
        self.checked_add(rhs.try_into().unwrap()).unwrap()
    }
}

impl Add<usize> for ShiftedU32 {
    type Output = Self;

    fn add(self, rhs: usize) -> Self::Output {
        debug_assert!(rhs <= u32::MAX as usize, "Addition overflow");
        ShiftedU32(unsafe { NonZeroU32::new_unchecked(self.0.get() + rhs as u32) })
    }
}

impl Sub<usize> for ShiftedU32 {
    type Output = Self;

    fn sub(self, rhs: usize) -> Self::Output {
        let result = self
            .0
            .get()
            .checked_sub(rhs as u32)
            .expect("Subtraction overflow");
        ShiftedU32(NonZeroU32::new(result).expect("Result of subtraction is zero"))
    }
}

impl Sub<u32> for ShiftedU32 {
    type Output = Self;
    fn sub(self, rhs: u32) -> Self::Output {
        self.checked_sub(rhs).unwrap()
    }
}

impl Sub<i32> for ShiftedU32 {
    type Output = Self;
    fn sub(self, rhs: i32) -> Self::Output {
        self.checked_sub(rhs.try_into().unwrap()).unwrap()
    }
}

impl AddAssign<u32> for ShiftedU32 {
    fn add_assign(&mut self, rhs: u32) {
        self.0 = unsafe { NonZeroU32::new_unchecked(self.0.get() + rhs) }
    }
}

impl AddAssign<usize> for ShiftedU32 {
    fn add_assign(&mut self, rhs: usize) {
        let rhs: u32 = rhs.try_into().unwrap();
        *self += rhs
    }
}

impl SubAssign<u32> for ShiftedU32 {
    fn sub_assign(&mut self, rhs: u32) {
        *self = *self - rhs;
    }
}

impl SubAssign<usize> for ShiftedU32 {
    fn sub_assign(&mut self, rhs: usize) {
        let rhs: u32 = rhs.try_into().unwrap();
        *self -= rhs;
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(from = "usize", into = "usize"))]
pub struct ShiftedU64(NonZeroU64);

impl Default for ShiftedU64 {
    fn default() -> Self {
        0usize.into()
    }
}

impl From<usize> for ShiftedU64 {
    fn from(value: usize) -> Self {
        debug_assert!(value + 1 < u64::MAX as usize);
        ShiftedU64(unsafe { NonZeroU64::new_unchecked((value + 1) as u64) })
    }
}

impl Into<usize> for ShiftedU64 {
    fn into(self) -> usize {
        self.0.get() as usize - 1
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(from = "usize", into = "usize"))]
pub struct ShiftedUsize(NonZeroUsize);

impl Default for ShiftedUsize {
    fn default() -> Self {
        0usize.into()
    }
}

impl From<usize> for ShiftedUsize {
    fn from(value: usize) -> Self {
        debug_assert!(value + 1 < usize::MAX as usize);
        ShiftedUsize(unsafe { NonZeroUsize::new_unchecked((value + 1) as usize) })
    }
}

impl Into<usize> for ShiftedUsize {
    fn into(self) -> usize {
        self.0.get() as usize - 1
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_checked_sub() {
        // Test successful subtraction
        let a = ShiftedU32::new(10);
        assert_eq!(a.checked_sub(5), Some(ShiftedU32::new(5)));

        // Test subtraction resulting in zero
        let b = ShiftedU32::new(5);
        assert_eq!(b.checked_sub(5), Some(ShiftedU32::new(0)));

        // Test subtraction resulting in underflow
        let c = ShiftedU32::new(3);
        assert_eq!(c.checked_sub(5), None);

        // Test subtraction with zero
        let d = ShiftedU32::new(7);
        assert_eq!(d.checked_sub(0), Some(d));

        // Test subtraction at the upper bound
        let max = ShiftedU32::new(u32::MAX - 1);
        assert_eq!(max.checked_sub(1), Some(ShiftedU32::new(u32::MAX - 2)));

        // Test subtraction at the lower bound
        let min = ShiftedU32::new(0);
        assert_eq!(min.checked_sub(1), None);
    }

    #[test]
    fn test_sub_usize() {
        let a = ShiftedU32::new(10);
        assert_eq!(a - 5usize, ShiftedU32::new(5));

        let b = ShiftedU32::new(100);
        assert_eq!(b - 50usize, ShiftedU32::new(50));

        let c = ShiftedU32::new(1);
        assert_eq!(c - 1usize, ShiftedU32::new(0));
    }

    #[test]
    #[should_panic(expected = "Subtraction overflow")]
    fn test_sub_usize_overflow() {
        let a = ShiftedU32::new(5);
        let _ = a - 10usize;
    }

    #[test]
    #[should_panic(expected = "Result of subtraction is zero")]
    fn test_zero_sub_one_usize_result() {
        let a = ShiftedU32::new(0);
        let _ = a - 1usize;
    }
}
