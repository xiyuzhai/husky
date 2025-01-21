use super::*;
use num_traits::identities::*;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VdFrac {
    numerator: VdInt,
    denominator: VdInt,
}

impl VdFrac {
    pub fn new(numerator: VdInt, denominator: VdInt) -> Self {
        assert!(!denominator.is_zero());
        let gcd = num_helpers::gcd(&numerator, &denominator);
        assert!(gcd.is_one());
        Self {
            numerator,
            denominator,
        }
    }

    pub fn new128(numerator: i128, denominator: i128) -> Self {
        Self::new(VdInt::from(numerator), VdInt::from(denominator))
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
