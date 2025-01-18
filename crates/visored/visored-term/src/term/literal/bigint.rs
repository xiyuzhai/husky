use either::*;
use num_bigint::Sign;
use std::str::FromStr;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VdBigIntData {
    inner: num_bigint::BigInt,
}

impl std::ops::Deref for VdBigIntData {
    type Target = num_bigint::BigInt;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl VdBigIntData {
    pub fn new(inner: num_bigint::BigInt) -> Self {
        debug_assert!(
            is_outside_i128_range(&inner),
            "BigInt value must be outside i128 range"
        );
        Self { inner }
    }

    pub fn new_or_i128(inner: num_bigint::BigInt) -> Either<Self, i128> {
        i128_from_bigint(&inner).map_or_else(|| Either::Left(Self { inner }), |i| Either::Right(i))
    }

    pub fn try_new(inner: num_bigint::BigInt) -> Result<Self, ()> {
        if is_outside_i128_range(&inner) {
            Ok(Self { inner })
        } else {
            Err(())
        }
    }
}

fn is_outside_i128_range(value: &num_bigint::BigInt) -> bool {
    value > &num_bigint::BigInt::from(i128::MAX) || value < &num_bigint::BigInt::from(i128::MIN)
}

fn i128_from_bigint(value: &num_bigint::BigInt) -> Option<i128> {
    if is_outside_i128_range(value) {
        None
    } else {
        Some(value.try_into().unwrap())
    }
}

impl FromStr for VdBigIntData {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        VdBigIntData::try_new(num_bigint::BigInt::from_str(s).unwrap())
    }
}

/// # helpers
impl VdBigIntData {
    pub fn sign(&self) -> Sign {
        self.inner.sign()
    }

    pub fn is_nonnegative(&self) -> bool {
        self.sign() != Sign::Minus
    }

    pub fn is_negative(&self) -> bool {
        self.sign() == Sign::Minus
    }
}

impl VdBigIntData {
    pub fn show_fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.inner)
    }
}

impl std::ops::Sub for &VdBigIntData {
    type Output = Either<VdBigIntData, i128>;

    fn sub(self, rhs: Self) -> Self::Output {
        let sub = &self.inner - &rhs.inner;
        VdBigIntData::new_or_i128(sub)
    }
}
