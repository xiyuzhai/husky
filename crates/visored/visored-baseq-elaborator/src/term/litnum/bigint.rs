use super::*;
use either::*;
use floated_sequential::{db::FloaterDb, floated};
use num_bigint::Sign;
use std::str::FromStr;

#[floated]
pub struct VdBsqBigInt<'sess> {
    #[return_ref]
    pub inner: VdBsqBigIntData,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VdBsqBigIntData {
    inner: num_bigint::BigInt,
}

impl std::ops::Deref for VdBsqBigIntData {
    type Target = num_bigint::BigInt;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<'sess> VdBsqBigInt<'sess> {
    pub fn new_or_i128_ref(inner: &num_bigint::BigInt, db: &'sess FloaterDb) -> Either<Self, i128> {
        match VdBsqBigIntData::new_or_i128_ref(inner) {
            Left(inner) => Either::Left(VdBsqBigInt::new_inner(inner, db)),
            Right(i) => Either::Right(i),
        }
    }

    pub fn new_or_i128_owned(
        inner: num_bigint::BigInt,
        db: &'sess FloaterDb,
    ) -> Either<Self, i128> {
        todo!()
    }
}

impl<'sess> From<Either<VdBsqBigInt<'sess>, i128>> for VdBsqLitnumTerm<'sess> {
    fn from(value: Either<VdBsqBigInt<'sess>, i128>) -> Self {
        match value {
            Left(bigint) => bigint.into(),
            Right(i) => i.into(),
        }
    }
}

impl<'sess> From<Either<VdBsqBigInt<'sess>, i128>> for VdBsqTerm<'sess> {
    fn from(value: Either<VdBsqBigInt<'sess>, i128>) -> Self {
        VdBsqTerm::Litnum(value.into())
    }
}

impl VdBsqBigIntData {
    pub fn new(inner: num_bigint::BigInt) -> Self {
        debug_assert!(
            is_outside_i128_range(&inner),
            "BigInt value must be outside i128 range"
        );
        Self { inner }
    }

    pub fn new_or_i128_ref(inner: &num_bigint::BigInt) -> Either<Self, i128> {
        i128_from_bigint(inner).map_or_else(
            || {
                Either::Left(Self {
                    inner: inner.clone(),
                })
            },
            |i| Either::Right(i),
        )
    }

    pub fn new_or_i128_owned(inner: num_bigint::BigInt) -> Either<Self, i128> {
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

impl FromStr for VdBsqBigIntData {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        VdBsqBigIntData::try_new(num_bigint::BigInt::from_str(s).unwrap())
    }
}

/// # helpers
impl VdBsqBigIntData {
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

impl VdBsqBigIntData {
    pub fn show_fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.inner)
    }
}

impl std::ops::Sub for &VdBsqBigIntData {
    type Output = Either<VdBsqBigIntData, i128>;

    fn sub(self, rhs: Self) -> Self::Output {
        let sub = &self.inner - &rhs.inner;
        VdBsqBigIntData::new_or_i128_owned(sub)
    }
}

impl<'sess> std::fmt::Debug for VdBsqBigInt<'sess> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("VdBsqBigInt(`")?;
        self.show_fmt(f)?;
        f.write_str("`)")
    }
}

impl<'sess> VdBsqBigInt<'sess> {
    pub fn sign(self) -> Sign {
        self.inner().sign()
    }

    pub fn is_nonnegative(self) -> bool {
        self.sign() != Sign::Minus
    }

    pub fn show_fmt(self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.inner().show_fmt(f)
    }
}

impl<'sess> VdBsqBigInt<'sess> {
    pub fn sub(self, rhs: Self, db: &'sess FloaterDb) -> VdBsqLitnumTerm<'sess> {
        let sub = self.inner() - rhs.inner();
        match sub {
            Left(inner) => VdBsqBigInt::new_inner(inner, db).into(),
            Right(i) => i.into(),
        }
    }
}
