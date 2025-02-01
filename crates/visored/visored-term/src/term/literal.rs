pub mod frac;
pub mod int;

use self::{frac::VdFrac, int::VdInt};
use super::*;
use crate::{menu::vd_ty_menu, ty::VdType};
use eterned::db::EternerDb;
use num_bigint::Sign;

// #[salsa::derive_debug_with_db]
// #[salsa::as_id]
// #[salsa::deref_id]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VdLiteral(VdTermId);

impl std::ops::Deref for VdLiteral {
    type Target = VdTermId;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl std::fmt::Display for VdLiteral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.show(f)
    }
}

impl std::fmt::Debug for VdLiteral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("VdLiteral(")?;
        self.show(f)?;
        f.write_str(")")
    }
}

impl VdLiteral {
    pub fn show(self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.data() {
            VdLiteralData::Int(n) => write!(f, "{}", n),
            VdLiteralData::Frac(frac) => write!(f, "{}", frac),
        }
    }
}

#[enum_class::from_variants]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VdLiteralData {
    Int(VdInt),
    Frac(VdFrac),
}

pub type VdSign = num_bigint::Sign;

impl std::fmt::Display for VdLiteralData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VdLiteralData::Int(n) => write!(f, "{}", n),
            VdLiteralData::Frac(frac) => write!(f, "{}", frac),
        }
    }
}

impl VdLiteral {
    pub fn new(data: VdLiteralData, db: &EternerDb) -> Self {
        Self(VdTermId::new(data.into(), db))
    }

    pub fn new_int128(i: i128, db: &EternerDb) -> Self {
        Self(VdTermId::new(VdLiteralData::Int(i.into()).into(), db))
    }

    pub fn new_frac128(numerator: i128, denominator: i128, db: &EternerDb) -> Self {
        Self(VdTermId::new(
            VdLiteralData::Frac(VdFrac::new128(numerator, denominator)).into(),
            db,
        ))
    }

    pub fn data(self) -> &'static VdLiteralData {
        match self.0.data() {
            VdTermData::Literal(data) => data,
            _ => unreachable!(),
        }
    }

    pub fn ty(self, db: &EternerDb) -> VdType {
        zfc_literal_ty(self, db)
    }

    pub fn is_zero(self) -> bool {
        self.is_i128(0)
    }

    pub fn is_one(self) -> bool {
        self.is_i128(1)
    }

    pub fn is_one_half(self) -> bool {
        self.is_frac128(1, 2)
    }

    pub fn is_neg_one(self) -> bool {
        self.is_i128(-1)
    }

    pub fn is_i128(self, i: i128) -> bool {
        match self.data() {
            VdLiteralData::Int(n) => match n.try_into() {
                Ok::<i128, _>(n) => n == i,
                Err(_) => false,
            },
            VdLiteralData::Frac(_) => false,
        }
    }

    pub fn is_frac128(self, numerator: i128, denominator: i128) -> bool {
        match self.data() {
            VdLiteralData::Frac(frac) => frac.is_frac128(numerator, denominator),
            _ => false,
        }
    }
}

fn zfc_literal_ty(literal: VdLiteral, db: &EternerDb) -> VdType {
    let data = literal.data();
    let menu = vd_ty_menu(db);
    match *data {
        VdLiteralData::Int(ref i) => match i.sign() {
            Sign::Minus => menu.int,
            Sign::NoSign | Sign::Plus => menu.nat,
        },
        VdLiteralData::Frac(_) => menu.rat,
    }
}

impl VdLiteral {
    pub fn inv(self, db: &EternerDb) -> Option<Self> {
        Some(Self::new(self.data().inv()?, db))
    }

    pub fn mul(self, other: Self, db: &EternerDb) -> Self {
        Self::new(self.data().mul(other.data()), db)
    }
}

impl VdLiteralData {
    pub fn add(&self, other: &Self) -> Self {
        match self {
            VdLiteralData::Int(slf) => match other {
                VdLiteralData::Int(other) => VdLiteralData::Int(slf + other),
                VdLiteralData::Frac(vd_frac) => todo!(),
            },
            VdLiteralData::Frac(f) => f.add_literal(other),
        }
    }

    pub fn mul(&self, other: &Self) -> Self {
        match self {
            VdLiteralData::Int(slf) => match other {
                VdLiteralData::Int(other) => VdLiteralData::Int(slf * other),
                VdLiteralData::Frac(other) => other.mul_bigint(slf),
            },
            VdLiteralData::Frac(slf) => match other {
                VdLiteralData::Int(other) => slf.mul_bigint(other),
                VdLiteralData::Frac(other) => slf.mul(other),
            },
        }
    }

    pub fn neg(&self) -> Self {
        match self {
            VdLiteralData::Int(n) => VdLiteralData::Int(-n),
            VdLiteralData::Frac(f) => VdLiteralData::Frac(-f),
        }
    }

    pub fn div(&self, other: &Self) -> Self {
        match self {
            VdLiteralData::Int(n) => todo!(),
            VdLiteralData::Frac(vd_frac) => todo!(),
        }
    }

    pub fn inv(&self) -> Option<Self> {
        match self {
            VdLiteralData::Int(n) => VdFrac::new_bigint_inv(n),
            VdLiteralData::Frac(f) => f.inv(),
        }
    }
}

impl std::ops::Mul for &VdLiteralData {
    type Output = VdLiteralData;

    fn mul(self, other: Self) -> Self::Output {
        self.mul(other)
    }
}
