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

    pub fn new_raw(raw_numerator: &VdInt, raw_denominator: &VdInt) -> VdLiteralData {
        if raw_denominator.is_zero() {
            return VdLiteralData::Int(0.into());
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
            VdLiteralData::Int(numerator)
        } else {
            VdLiteralData::Frac(Self::new(numerator, denominator))
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
    pub fn add_literal(&self, other: &VdLiteralData) -> VdLiteralData {
        match other {
            VdLiteralData::Int(big_int) => self.add_bigint(big_int).into(),
            VdLiteralData::Frac(vd_frac) => self.add_frac(vd_frac),
        }
    }

    pub fn add_bigint(&self, big_int: &VdInt) -> Self {
        Self::new(
            &self.numerator + big_int * &self.denominator,
            self.denominator.clone(),
        )
    }

    pub fn add_frac(&self, other: &VdFrac) -> VdLiteralData {
        Self::new_raw(
            &(&self.numerator * &other.denominator + &other.numerator * &self.denominator),
            &(&self.denominator * &other.denominator),
        )
    }

    pub fn mul_bigint(&self, big_int: &VdInt) -> VdLiteralData {
        VdFrac::new_raw(&(&self.numerator * big_int), &self.denominator)
    }
}

impl std::ops::Neg for VdFrac {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::new(-self.numerator, self.denominator)
    }
}

impl std::ops::Neg for &VdFrac {
    type Output = VdFrac;

    fn neg(self) -> Self::Output {
        VdFrac::new(-&self.numerator, self.denominator.clone())
    }
}
