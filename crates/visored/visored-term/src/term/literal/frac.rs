use super::*;
use num_traits::{identities::*, *};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VdFrac {
    numerator: VdInt,
    denominator: VdInt,
}

impl VdFrac {
    pub fn new(numerator: VdInt, denominator: VdInt) -> Self {
        assert!(!denominator.is_zero());
        assert!(denominator.is_positive());
        assert!(!denominator.is_one());
        let gcd = num_helpers::gcd(&numerator, &denominator);
        assert!(gcd.is_one());
        Self {
            numerator,
            denominator,
        }
    }

    pub fn new_raw(raw_numerator: &VdInt, raw_denominator: &VdInt) -> Either<Self, VdInt> {
        if raw_denominator.is_zero() {
            return Right(0.into());
        }
        let gcd = num_helpers::gcd(raw_numerator, raw_denominator);
        let gcd = match raw_denominator.sign() {
            Sign::Minus => match gcd.sign() {
                Sign::Minus => gcd,
                Sign::NoSign => todo!(),
                Sign::Plus => -gcd,
            },
            Sign::NoSign => todo!(),
            Sign::Plus => match gcd.sign() {
                Sign::Minus => -gcd,
                Sign::NoSign => todo!(),
                Sign::Plus => gcd,
            },
        };
        let numerator = raw_numerator / &gcd;
        let denominator = raw_denominator / &gcd;
        if denominator.is_one() {
            Right(numerator)
        } else {
            Left(Self::new(numerator, denominator))
        }
    }

    pub fn new128(numerator: i128, denominator: i128) -> Self {
        Self::new(VdInt::from(numerator), VdInt::from(denominator))
    }

    pub fn is_frac128(&self, numerator: i128, denominator: i128) -> bool {
        self.numerator.to_i128() == Some(numerator)
            && self.denominator.to_i128() == Some(denominator)
    }

    pub fn new_bigint_inv(n: &VdInt) -> Option<VdLiteralData> {
        if n.is_one() {
            Some(VdLiteralData::Int(1.into()))
        } else if n == &(-1).into() {
            Some(VdLiteralData::Int((-1).into()))
        } else {
            match n.sign() {
                Sign::Minus => Some(VdLiteralData::Frac(VdFrac::new((-1).into(), -n))),
                Sign::NoSign => None,
                Sign::Plus => Some(VdLiteralData::Frac(VdFrac::new(1.into(), n.clone()))),
            }
        }
    }
}

impl VdFrac {
    pub fn numerator(&self) -> &VdInt {
        &self.numerator
    }

    pub fn denominator(&self) -> &VdInt {
        &self.denominator
    }
}

impl std::fmt::Display for VdFrac {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} / {})", self.numerator, self.denominator)
    }
}

impl VdFrac {
    pub fn mul_bigint(&self, big_int: &VdInt) -> Either<VdFrac, VdInt> {
        VdFrac::new_raw(&(&self.numerator * big_int), &self.denominator)
    }
}
