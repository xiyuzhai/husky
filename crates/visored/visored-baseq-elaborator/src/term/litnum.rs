pub mod bigint;
pub mod bigrat;
pub mod frac128;

use self::{
    bigint::VdBsqBigInt,
    frac128::{Div, VdBsqFrac128},
};
use super::*;
use crate::foundations::num::VdBsqSign;
use num_bigint::Sign;
use product::VdBsqProductTerm;
use std::num::NonZeroU128;
use visored_opr::precedence::{VdPrecedence, VdPrecedenceRange};

#[enum_class::from_variants]
#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq)]
pub enum VdBsqLitnumTerm<'sess> {
    Int128(i128),
    BigInt(VdBsqBigInt<'sess>),
    Frac128(VdBsqFrac128),
}

impl<'sess> PartialOrd for VdBsqLitnumTerm<'sess> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<'sess> Ord for VdBsqLitnumTerm<'sess> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        match *other {
            VdBsqLitnumTerm::Int128(other) => self.cmp_with_i128(other),
            VdBsqLitnumTerm::BigInt(other) => self.cmp_with_bigint(other),
            VdBsqLitnumTerm::Frac128(other) => self.cmp_with_frac128(other),
        }
    }
}

#[test]
fn vd_bsq_litnum_term_ord_works() {
    #[track_caller]
    fn t<'sess>(a: impl Into<VdBsqLitnumTerm<'sess>>, b: impl Into<VdBsqLitnumTerm<'sess>>) {
        let a = a.into();
        let b = b.into();
        assert!(a < b);
        assert!(b > a);
        assert!(a <= b);
        assert!(b >= a);
        assert!(a == a);
        assert!(b == b);
        assert!(a != b);
        assert!(b != a);
    }
    use self::frac128::Div;

    t(0, 1);
    t(0, 2);
    t(-1, 1);
    t(-1, Div(1, 2));
    t(Div(1, 2), 1);
    t(-1, Div(-1, 2));
    t(Div(-3, 2), -1);
    t(Div(2, 3), Div(3, 2));
    t(Div(-3, 2), Div(-2, 3));
    t(Div(1, 5), 5);
    t(-5, Div(-1, 5));
}

impl<'sess> VdBsqLitnumTerm<'sess> {
    pub fn eqs_frac128(self, numerator: i128, denominator: i128) -> bool {
        match self {
            VdBsqLitnumTerm::Int128(_) | VdBsqLitnumTerm::BigInt(_) => false,
            VdBsqLitnumTerm::Frac128(frac128) => frac128.eqs_frac128(numerator, denominator),
        }
    }

    pub fn neg(self, db: &FloaterDb) -> Self {
        match self {
            VdBsqLitnumTerm::Int128(i) => VdBsqLitnumTerm::Int128(-i),
            VdBsqLitnumTerm::BigInt(i) => {
                todo!()
            }
            VdBsqLitnumTerm::Frac128(f) => VdBsqLitnumTerm::Frac128(-f),
        }
    }

    pub fn sign(self, db: &FloaterDb) -> VdBsqSign {
        match self {
            VdBsqLitnumTerm::Int128(i) => {
                if i > 0 {
                    VdBsqSign::Plus
                } else if i < 0 {
                    VdBsqSign::Minus
                } else {
                    VdBsqSign::NoSign
                }
            }
            VdBsqLitnumTerm::BigInt(vd_bsq_big_int) => todo!(),
            VdBsqLitnumTerm::Frac128(slf) => slf.sign(),
        }
    }

    pub fn with_sign(self, sign: VdBsqSign, db: &FloaterDb) -> Self {
        if self.sign(db) == sign {
            self
        } else {
            match sign {
                Sign::Minus | Sign::Plus => self.neg(db),
                Sign::NoSign => todo!(),
            }
        }
    }

    pub fn add(self, rhs: Self, db: &'sess FloaterDb) -> VdBsqLitnumTerm<'sess> {
        if self.is_zero() {
            return rhs;
        }
        match self {
            VdBsqLitnumTerm::Int128(slf) => match rhs {
                VdBsqLitnumTerm::Int128(rhs) => match slf.checked_add(rhs) {
                    Some(sum) => VdBsqLitnumTerm::Int128(sum),
                    None => todo!(),
                },
                VdBsqLitnumTerm::BigInt(i) => {
                    use husky_print_utils::p;
                    p!(self, rhs);
                    todo!()
                }
                VdBsqLitnumTerm::Frac128(rhs) => rhs.add_i128(slf, db),
            },
            VdBsqLitnumTerm::BigInt(i) => todo!(),
            VdBsqLitnumTerm::Frac128(slf) => match rhs {
                VdBsqLitnumTerm::Int128(_) => todo!(),
                VdBsqLitnumTerm::BigInt(vd_bsq_big_int) => todo!(),
                VdBsqLitnumTerm::Frac128(rhs) => slf.add(rhs, db),
            },
        }
    }

    pub fn add_assign(&mut self, rhs: Self, db: &'sess FloaterDb) {
        *self = self.add(rhs, db);
    }

    pub fn sub(self, rhs: Self, db: &'sess FloaterDb) -> Self {
        if self.is_zero() {
            return rhs.neg(db);
        }
        if rhs.is_zero() {
            return self;
        }
        if self == rhs {
            return 0.into();
        }
        match rhs {
            VdBsqLitnumTerm::Int128(rhs) => match self {
                VdBsqLitnumTerm::Int128(slf) => match slf.checked_sub(rhs) {
                    Some(sub) => VdBsqLitnumTerm::Int128(sub),
                    None => todo!(),
                },
                VdBsqLitnumTerm::BigInt(vd_bsq_big_int) => todo!(),
                VdBsqLitnumTerm::Frac128(slf) => slf.sub_i128(rhs, db),
            },
            VdBsqLitnumTerm::BigInt(vd_bsq_big_int) => todo!(),
            VdBsqLitnumTerm::Frac128(f) => self.sub_frac128(f, db),
        }
    }

    pub fn sub_frac128(self, rhs: VdBsqFrac128, db: &'sess FloaterDb) -> Self {
        match self {
            VdBsqLitnumTerm::Int128(_) => todo!(),
            VdBsqLitnumTerm::BigInt(vd_bsq_big_int) => todo!(),
            VdBsqLitnumTerm::Frac128(vd_bsq_frac128) => todo!(),
        }
    }

    pub fn sub_assign(&mut self, rhs: Self, db: &'sess FloaterDb) {
        *self = self.sub(rhs, db);
    }

    pub fn mul(self, rhs: Self, db: &'sess FloaterDb) -> Self {
        match rhs {
            VdBsqLitnumTerm::Int128(rhs) => self.mul128(rhs, db),
            VdBsqLitnumTerm::BigInt(rhs) => todo!(),
            VdBsqLitnumTerm::Frac128(rhs) => self.mul_frac128(rhs, db),
        }
    }

    pub fn mul128(self, rhs: i128, db: &'sess FloaterDb) -> Self {
        match self {
            VdBsqLitnumTerm::Int128(i) => match i.checked_mul(rhs) {
                Some(product) => VdBsqLitnumTerm::Int128(product),
                None => todo!(),
            },
            VdBsqLitnumTerm::BigInt(i) => todo!(),
            VdBsqLitnumTerm::Frac128(slf) => slf.mul_i128(rhs, db),
        }
    }

    pub fn mul_frac128(self, rhs: VdBsqFrac128, db: &'sess FloaterDb) -> Self {
        match self {
            VdBsqLitnumTerm::Int128(slf) => {
                let Some(numerator) = slf.checked_mul(rhs.numerator()) else {
                    todo!()
                };
                VdBsqFrac128::new128(numerator, rhs.denominator())
                    .expect("denominator can't be nonzero")
            }
            VdBsqLitnumTerm::BigInt(slf) => todo!(),
            VdBsqLitnumTerm::Frac128(slf) => slf.mul(rhs, db),
        }
    }

    pub fn mul_product_base(
        self,
        rhs: VdBsqProductStem<'sess>,
        db: &'sess FloaterDb,
    ) -> VdBsqNumTerm<'sess> {
        if self.is_zero() {
            return VdBsqNumTerm::ZERO;
        }
        VdBsqProductTerm::new(self, rhs).into()
    }

    pub fn mul_assign(&mut self, rhs: Self, db: &'sess FloaterDb) {
        *self = self.mul(rhs, db);
        // match *self {
        //     VdBsqLitnumTerm::ZERO => (),
        //     VdBsqLitnumTerm::ONE => *self = rhs,
        //     VdBsqLitnumTerm::Int128(slf) => match rhs {
        //         VdBsqLitnumTerm::Int128(rhs) => match slf.checked_mul(rhs) {
        //             Some(product) => *self = VdBsqLitnumTerm::Int128(product),
        //             None => todo!(),
        //         },
        //         VdBsqLitnumTerm::BigInt(i) => todo!(),
        //         VdBsqLitnumTerm::Frac128(f) => todo!(),
        //     },
        //     VdBsqLitnumTerm::BigInt(i) => todo!(),
        //     VdBsqLitnumTerm::Frac128(f) => *self = f.mul_litn(rhs, db),
        // }
    }

    pub fn div(
        self,
        rhs: VdBsqLitnumTerm<'sess>,
        db: &'sess FloaterDb,
    ) -> Option<VdBsqLitnumTerm<'sess>> {
        match rhs {
            VdBsqLitnumTerm::Int128(rhs) => self.div128(rhs, db),
            VdBsqLitnumTerm::BigInt(rhs) => todo!(),
            VdBsqLitnumTerm::Frac128(rhs) => self.div_frac128(rhs, db),
        }
    }

    pub fn div128(self, rhs: i128, db: &'sess FloaterDb) -> Option<VdBsqLitnumTerm<'sess>> {
        if rhs == 0 {
            return None;
        }
        if rhs == 1 {
            return Some(self);
        }
        match self {
            VdBsqLitnumTerm::Int128(i) => VdBsqFrac128::new128(i, rhs).unwrap().into(),
            VdBsqLitnumTerm::BigInt(vd_bsq_big_int) => todo!(),
            VdBsqLitnumTerm::Frac128(vd_bsq_frac128) => todo!(),
        }
    }

    pub fn div_frac128(
        self,
        rhs: VdBsqFrac128,
        db: &'sess FloaterDb,
    ) -> Option<VdBsqLitnumTerm<'sess>> {
        Some(self.mul_frac128(rhs.inverse(), db))
    }

    pub fn div_assign(&mut self, rhs: Self, db: &FloaterDb) {
        match *self {
            VdBsqLitnumTerm::Int128(slf) => match rhs {
                VdBsqLitnumTerm::Int128(rhs) => *self = VdBsqFrac128::new128(slf, rhs).unwrap(),
                VdBsqLitnumTerm::BigInt(i) => todo!(),
                VdBsqLitnumTerm::Frac128(_) => todo!(),
            },
            VdBsqLitnumTerm::BigInt(i) => todo!(),
            VdBsqLitnumTerm::Frac128(_) => todo!(),
        }
    }

    pub fn pow(self, exponent: VdBsqLitnumTerm<'sess>, db: &'sess FloaterDb) -> Self {
        match exponent {
            VdBsqLitnumTerm::Int128(exponent) => self.pow128(exponent, db),
            VdBsqLitnumTerm::BigInt(exponent) => todo!(),
            VdBsqLitnumTerm::Frac128(exponent) => todo!(),
        }
    }

    pub fn pow128(self, exponent: i128, db: &'sess FloaterDb) -> Self {
        match self {
            VdBsqLitnumTerm::Int128(i) => {
                if exponent > 0 {
                    let exponent: u32 = match exponent.try_into() {
                        Ok(exponent) => exponent,
                        Err(_) => todo!(),
                    };
                    match i.checked_pow(exponent) {
                        Some(pow) => VdBsqLitnumTerm::Int128(pow),
                        None => todo!(),
                    }
                } else {
                    let neg_exponent: u32 = match (-exponent).try_into() {
                        Ok(neg_exponent) => neg_exponent,
                        Err(_) => todo!(),
                    };
                    let Some(raw_denominator) = i.checked_pow(neg_exponent) else {
                        todo!()
                    };
                    VdBsqFrac128::new128(1, raw_denominator).unwrap()
                }
            }
            VdBsqLitnumTerm::BigInt(i) => todo!(),
            VdBsqLitnumTerm::Frac128(slf) => slf.pow128(exponent, db),
        }
    }
}

#[test]
fn vd_bsq_litnum_term_sub_works() {
    #[track_caller]
    fn t<'sess>(
        a: impl Into<VdBsqLitnumTerm<'sess>>,
        b: impl Into<VdBsqLitnumTerm<'sess>>,
        c: impl Into<VdBsqLitnumTerm<'sess>>,
        db: &'sess FloaterDb,
    ) {
        assert_eq!(a.into().sub(b.into(), db), c.into());
    }
    let db = &FloaterDb::default();
    t(2, 3, -1, db);
    t(2, -3, 5, db);
    t(Div(1, 2), 3, Div(-5, 2), db);
    t(Div(1, 2), -3, Div(7, 2), db);
}

#[test]
fn vd_bsq_litnum_term_pow128_works() {
    #[track_caller]
    fn t<'sess>(
        a: impl Into<VdBsqLitnumTerm<'sess>>,
        b: impl Into<i128>,
        c: impl Into<VdBsqLitnumTerm<'sess>>,
        db: &'sess FloaterDb,
    ) {
        assert_eq!(a.into().pow128(b.into(), db), c.into());
    }

    let db = &FloaterDb::default();
    t(2, 3, 8, db);
    t(2, -3, Div(1, 8), db);
    t(Div(1, 2), 3, Div(1, 8), db);
    t(Div(1, 2), -3, 8, db);
}

impl<'sess> VdBsqLitnumTerm<'sess> {
    pub const ZERO: Self = Self::Int128(0);
    pub const ONE: Self = Self::Int128(1);
    pub const NEG_ONE: Self = Self::Int128(-1);
}

impl<'sess> VdBsqLitnumTerm<'sess> {
    pub fn is_zero(self) -> bool {
        self.eqs_i128(0)
    }

    pub fn is_nonzero(self) -> bool {
        !self.is_zero()
    }

    pub fn is_one(self) -> bool {
        self.eqs_i128(1)
    }

    pub fn eqs_i128(self, i0: i128) -> bool {
        match self {
            VdBsqLitnumTerm::Int128(i) => i == i0,
            _ => false,
        }
    }

    pub fn inverse(self) -> Option<Self> {
        match self {
            VdBsqLitnumTerm::Int128(slf) => {
                if slf == 0 {
                    None
                } else if slf == 1 || slf == -1 {
                    Some(slf.into())
                } else {
                    match VdBsqFrac128::new_i128_inverse(slf) {
                        Some(frac) => Some(frac.into()),
                        None => Some(todo!("use big frac")),
                    }
                }
            }
            VdBsqLitnumTerm::BigInt(slf) => todo!(),
            VdBsqLitnumTerm::Frac128(slf) => {
                VdBsqFrac128::new128(slf.denominator(), slf.numerator())
            }
        }
    }
}

#[test]
fn vd_bsq_litnum_term_inverse_works() {
    assert!(VdBsqLitnumTerm::Int128(0).inverse().is_none());

    #[track_caller]
    fn t<'sess>(
        input: impl Into<VdBsqLitnumTerm<'sess>>,
        expected: impl Into<VdBsqLitnumTerm<'sess>>,
    ) {
        let litnum = input.into();
        let inverse = litnum.inverse();
        assert!(inverse.is_some());
        assert_eq!(inverse.unwrap(), expected.into());
    }

    use self::frac128::Div;

    t(1, 1);
    t(-1, -1);
    t(Div(2, 3), Div(3, 2));
    t(Div(-2, 3), Div(-3, 2));
    t(5, Div(1, 5));
    t(-5, Div(-1, 5));
}

impl<'sess> VdBsqLitnumTerm<'sess> {
    pub fn show_fmt(
        self,
        precedence_range: VdPrecedenceRange,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        let outer_precedence = self.outer_precedence();
        if precedence_range.contains(outer_precedence) {
            self.show_fmt_inner(f)
        } else {
            f.write_str("(")?;
            self.show_fmt_inner(f)?;
            f.write_str(")")
        }
    }

    pub fn outer_precedence(self) -> VdPrecedence {
        match self {
            VdBsqLitnumTerm::Int128(i) => {
                if i >= 0 {
                    VdPrecedence::ATOM
                } else {
                    VdPrecedence::ADD_SUB
                }
            }
            VdBsqLitnumTerm::BigInt(i) => {
                if i.is_nonnegative() {
                    VdPrecedence::ATOM
                } else {
                    VdPrecedence::ADD_SUB
                }
            }
            VdBsqLitnumTerm::Frac128(_) => VdPrecedence::MUL_DIV,
        }
    }

    fn show_fmt_inner(self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VdBsqLitnumTerm::Int128(i) => write!(f, "{}", i),
            VdBsqLitnumTerm::BigInt(i) => i.show_fmt(f),
            VdBsqLitnumTerm::Frac128(i) => i.show_fmt(f),
        }
    }
}

impl<'sess> VdBsqLitnumTerm<'sess> {
    pub fn cmp_with_zero(self, kind: VdBsqComparisonOpr) -> bool {
        match self {
            VdBsqLitnumTerm::Int128(i) => match kind {
                VdBsqComparisonOpr::EQ => i == 0,
                VdBsqComparisonOpr::NE => i != 0,
                VdBsqComparisonOpr::LT => i < 0,
                VdBsqComparisonOpr::GT => i > 0,
                VdBsqComparisonOpr::LE => i <= 0,
                VdBsqComparisonOpr::GE => i >= 0,
            },
            VdBsqLitnumTerm::BigInt(i) => todo!(),
            VdBsqLitnumTerm::Frac128(_) => todo!(),
        }
    }

    pub fn cmp_with_i128(self, i: i128) -> std::cmp::Ordering {
        match self {
            VdBsqLitnumTerm::Int128(slf) => slf.cmp(&i),
            VdBsqLitnumTerm::BigInt(slf) => todo!(),
            VdBsqLitnumTerm::Frac128(slf) => slf.cmp_with_i128(i),
        }
    }

    pub fn cmp_with_bigint(self, i: VdBsqBigInt<'sess>) -> std::cmp::Ordering {
        match self {
            VdBsqLitnumTerm::Int128(i) => todo!(),
            VdBsqLitnumTerm::BigInt(vd_bsq_big_int) => todo!(),
            VdBsqLitnumTerm::Frac128(vd_bsq_frac128) => todo!(),
        }
    }

    pub fn cmp_with_frac128(self, other: VdBsqFrac128) -> std::cmp::Ordering {
        match self {
            VdBsqLitnumTerm::Int128(slf) => other.cmp_with_i128(slf).reverse(),
            VdBsqLitnumTerm::BigInt(vd_bsq_big_int) => todo!(),
            VdBsqLitnumTerm::Frac128(slf) => slf.cmp(&other),
        }
    }
}

impl<'db, 'sess> VdBsqLitnumTerm<'sess> {
    pub(crate) fn transcribe_data_and_ty(
        self,
        elaborator: &VdBsqElaboratorInner<'db, 'sess>,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> (VdMirExprData, VdType) {
        let db = elaborator.eterner_db();
        match self {
            VdBsqLitnumTerm::Int128(i) => {
                if i >= 0 {
                    (
                        VdMirExprData::Literal(VdLiteral::new_int128(i, db)),
                        elaborator.ty_menu().nat,
                    )
                } else {
                    (
                        VdMirExprData::Literal(VdLiteral::new_int128(i, db)),
                        elaborator.ty_menu().int,
                    )
                }
            }
            VdBsqLitnumTerm::BigInt(vd_bsq_big_int) => todo!(),
            VdBsqLitnumTerm::Frac128(f) => {
                let a = VdMirExprData::Application {
                    function: VdMirFunc::NormalBaseBinaryOpr(elaborator.signature_menu().rat_div),
                    arguments: hypothesis_constructor.mk_exprs([
                        VdMirExprEntry::new(
                            VdMirExprData::Literal(VdLiteral::new_int128(f.numerator(), db)),
                            if f.numerator() >= 0 {
                                elaborator.ty_menu().nat
                            } else {
                                elaborator.ty_menu().int
                            },
                            Some(elaborator.ty_menu().rat),
                        ),
                        VdMirExprEntry::new(
                            VdMirExprData::Literal(VdLiteral::new_int128(f.denominator(), db)),
                            elaborator.ty_menu().nat,
                            Some(elaborator.ty_menu().rat),
                        ),
                    ]),
                };
                (a, elaborator.ty_menu().rat)
            }
        }
    }
}
