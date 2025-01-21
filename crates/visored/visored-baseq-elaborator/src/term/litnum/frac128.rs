use super::*;
use eterned::db::EternerDb;
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VdBsqFrac128 {
    numerator: i128,
    denominator: i128,
}

impl Into<VdFrac> for VdBsqFrac128 {
    fn into(self) -> VdFrac {
        VdFrac::new128(self.numerator, self.denominator)
    }
}

impl VdBsqFrac128 {
    pub fn into_vd_literal(self, db: &EternerDb) -> VdLiteral {
        VdLiteral::new_frac128(self.numerator, self.denominator, db)
    }
}

impl VdBsqFrac128 {
    pub fn from_vd_frac(frac: &VdFrac) -> Option<Self> {
        let numerator = frac.numerator().to_i128()?;
        let denominator = frac.denominator().to_i128()?;
        assert!(numerator.abs().gcd(&denominator).is_one());
        Some(Self {
            numerator,
            denominator,
        })
    }
}

pub struct Div(pub i128, pub i128);

impl<'sess> Into<VdBsqLitnumTerm<'sess>> for Div {
    fn into(self) -> VdBsqLitnumTerm<'sess> {
        let litnum = VdBsqFrac128::new128(self.0, self.1).unwrap();
        match litnum {
            VdBsqLitnumTerm::Frac128(vd_bsq_frac128) => {
                assert!(vd_bsq_frac128.numerator() == self.0);
                assert!(vd_bsq_frac128.denominator() == self.1);
            }
            _ => panic!(),
        }
        litnum
    }
}

impl Into<VdBsqFrac128> for Div {
    fn into(self) -> VdBsqFrac128 {
        match VdBsqFrac128::new128(self.0, self.1).unwrap() {
            VdBsqLitnumTerm::Frac128(f) => f,
            _ => panic!(),
        }
    }
}

impl VdBsqFrac128 {
    pub fn new128<'sess>(
        raw_numerator: i128,
        raw_denominator: i128,
    ) -> Option<VdBsqLitnumTerm<'sess>> {
        if raw_denominator == 0 {
            return None;
        }
        let (numerator, denominator) = reduce(raw_numerator, raw_denominator);
        debug_assert!(denominator > 0);
        debug_assert_eq!(
            BigInt::from(denominator) * BigInt::from(raw_numerator),
            BigInt::from(numerator) * BigInt::from(raw_denominator)
        );
        if denominator == 1 {
            Some(numerator.into())
        } else {
            Some(
                Self {
                    numerator,
                    denominator,
                }
                .into(),
            )
        }
    }

    pub fn new_i128_inverse(i: i128) -> Option<VdBsqFrac128> {
        debug_assert!(i != 0);
        if i > 0 {
            Some(Self {
                numerator: 1,
                denominator: i,
            })
        } else {
            Some(Self {
                numerator: -1,
                denominator: i.checked_neg()?,
            })
        }
    }
}

fn reduce(raw_numerator: i128, raw_denominator: i128) -> (i128, i128) {
    if raw_numerator == i128::MIN || raw_denominator == i128::MIN {
        todo!("needs careful handling")
    } else {
        use num_integer::Integer;

        let gcd = raw_numerator.abs().gcd(&raw_denominator.abs());
        let (numerator, denominator) = (raw_numerator / gcd, raw_denominator / gcd);
        if denominator < 0 {
            (-numerator, -denominator)
        } else {
            (numerator, denominator)
        }
    }
}

impl VdBsqFrac128 {
    pub fn numerator(self) -> i128 {
        self.numerator
    }

    pub fn denominator(self) -> i128 {
        self.denominator
    }

    pub fn sign(self) -> VdBsqSign {
        if self.numerator > 0 {
            VdBsqSign::Plus
        } else if self.numerator < 0 {
            VdBsqSign::Minus
        } else {
            VdBsqSign::NoSign
        }
    }

    pub fn eqs_frac128(self, numerator: i128, denominator: i128) -> bool {
        self.numerator == numerator && self.denominator == denominator
    }

    pub fn add<'sess>(self, rhs: Self, db: &'sess FloaterDb) -> VdBsqLitnumTerm<'sess> {
        // First multiply denominators to get common denominator
        let Some(common_denominator) = self.denominator.checked_mul(rhs.denominator) else {
            todo!()
        };

        // Scale up each numerator
        let Some(lhs_scaled) = self.numerator.checked_mul(rhs.denominator) else {
            todo!()
        };
        let Some(rhs_scaled) = rhs.numerator.checked_mul(self.denominator) else {
            todo!()
        };

        // Add the scaled numerators
        let Some(raw_numerator) = lhs_scaled.checked_add(rhs_scaled) else {
            todo!()
        };

        // Create new reduced fraction
        Self::new128(raw_numerator, common_denominator).unwrap()
    }

    pub fn add_i128<'sess>(self, rhs: i128, db: &'sess FloaterDb) -> VdBsqLitnumTerm<'sess> {
        let Some(rhs_scaled) = rhs.checked_mul(self.denominator) else {
            todo!()
        };
        let Some(raw_numerator) = self.numerator.checked_add(rhs_scaled) else {
            todo!()
        };
        Self::new128(raw_numerator, self.denominator).unwrap()
    }

    pub fn sub_i128<'sess>(self, rhs: i128, db: &'sess FloaterDb) -> VdBsqLitnumTerm<'sess> {
        let Some(rhs_scaled) = rhs.checked_mul(self.denominator) else {
            todo!()
        };
        let Some(raw_numerator) = self.numerator.checked_sub(rhs_scaled) else {
            todo!()
        };
        Self::new128(raw_numerator, self.denominator).unwrap()
    }

    pub fn inverse(self) -> Self {
        assert!(self.numerator != 0);
        if self.numerator > 0 {
            Self {
                numerator: self.denominator,
                denominator: self.numerator,
            }
        } else {
            Self {
                numerator: self.denominator.checked_neg().unwrap(),
                denominator: match self.numerator.checked_neg() {
                    Some(neg_numerator) => neg_numerator,
                    None => todo!(),
                },
            }
        }
    }

    pub fn mul<'sess>(self, rhs: Self, db: &'sess FloaterDb) -> VdBsqLitnumTerm<'sess> {
        let Some(raw_numerator) = self.numerator.checked_mul(rhs.numerator) else {
            todo!()
        };
        let Some(raw_denominator) = self.denominator.checked_mul(rhs.denominator) else {
            todo!()
        };
        Self::new128(raw_numerator, raw_denominator).unwrap()
    }

    pub fn pow128<'sess>(self, exponent: i128, db: &'sess FloaterDb) -> VdBsqLitnumTerm<'sess> {
        if exponent == 0 {
            return 1.into();
        }
        if exponent == 1 {
            return self.into();
        }
        if exponent < 0 {
            return self.inverse().pow128(-exponent, db);
        }
        let exponent: u32 = match exponent.try_into() {
            Ok(exponent) => exponent,
            Err(_) => todo!(),
        };
        let Some(raw_numerator) = self.numerator.checked_pow(exponent) else {
            todo!()
        };
        let Some(raw_denominator) = self.denominator.checked_pow(exponent) else {
            todo!()
        };
        Self::new128(raw_numerator, raw_denominator).unwrap()
    }
}

#[test]
fn vd_bsq_frac128_add_works() {
    fn t<'sess>(
        a: impl Into<VdBsqLitnumTerm<'sess>>,
        b: impl Into<VdBsqLitnumTerm<'sess>>,
        c: impl Into<VdBsqLitnumTerm<'sess>>,
        db: &'sess FloaterDb,
    ) {
        assert_eq!(a.into().add(b.into(), db), c.into());
    }
    let db = &FloaterDb::default();
    t(Div(1, 2), Div(3, 4), Div(5, 4), db);
    t(Div(1, 2), Div(1, 2), 1, db);
    t(Div(1, 2), Div(-1, 2), 0, db);
}

impl std::ops::Neg for VdBsqFrac128 {
    type Output = Self;

    fn neg(self) -> Self {
        Self {
            numerator: -self.numerator,
            denominator: self.denominator,
        }
    }
}

impl<'sess> VdBsqFrac128 {
    pub fn cmp_with_i128(self, other: i128) -> std::cmp::Ordering {
        match self.denominator.checked_mul(other) {
            Some(other_mul_denominator) => self.numerator.cmp(&other_mul_denominator),
            None => todo!(),
        }
    }

    pub fn mul_litn(
        self,
        rhs: VdBsqLitnumTerm<'sess>,
        db: &'sess FloaterDb,
    ) -> VdBsqLitnumTerm<'sess> {
        match rhs {
            VdBsqLitnumTerm::Int128(i) => self.mul_i128(i, db),
            VdBsqLitnumTerm::BigInt(vd_bsq_litnum_term_big_int) => todo!(),
            VdBsqLitnumTerm::Frac128(vd_bsq_frac128) => todo!(),
        }
    }

    pub fn mul_i128(self, rhs: i128, db: &'sess FloaterDb) -> VdBsqLitnumTerm<'sess> {
        let Self {
            numerator,
            denominator,
        } = self;
        match numerator.checked_mul(rhs) {
            Some(raw_numerator) => Self::new128(raw_numerator, denominator).unwrap(),
            None => todo!(),
        }
    }
}

impl<'sess> VdBsqFrac128 {
    pub fn show_fmt(self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} / {}", self.numerator, self.denominator)
    }
}
