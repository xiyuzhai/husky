pub mod bigint;
pub mod frac;
pub mod special_constant;

use eterned::db::EternerDb;
use num_bigint::Sign;

use self::special_constant::VdSpecialConstant;
use super::*;
use crate::{menu::vd_ty_menu, ty::VdType};

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
            VdLiteralData::Integer(n) => write!(f, "{}", n),
            VdLiteralData::Float(s) => write!(f, "{}", s),
            VdLiteralData::SpecialConstant(vd_special_constant) => todo!(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VdLiteralData {
    Integer(VdInteger),
    Float(String),
    SpecialConstant(VdSpecialConstant),
}

pub type VdInteger = num_bigint::BigInt;
pub type VdSign = num_bigint::Sign;

impl std::fmt::Display for VdLiteralData {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VdLiteralData::Integer(n) => write!(f, "{}", n),
            VdLiteralData::Float(n) => write!(f, "{}", n),
            VdLiteralData::SpecialConstant(n) => todo!(),
        }
    }
}

impl VdLiteral {
    pub fn new(data: VdLiteralData, db: &EternerDb) -> Self {
        Self(VdTermId::new(data.into(), db))
    }

    pub fn new_int128(i: i128, db: &EternerDb) -> Self {
        Self(VdTermId::new(VdLiteralData::Integer(i.into()).into(), db))
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
}

fn zfc_literal_ty(literal: VdLiteral, db: &EternerDb) -> VdType {
    let data = literal.data();
    let menu = vd_ty_menu(db);
    match *data {
        VdLiteralData::Integer(ref i) => match i.sign() {
            Sign::Minus => menu.int,
            Sign::NoSign | Sign::Plus => menu.nat,
        },
        VdLiteralData::Float(_) => menu.rat,
        VdLiteralData::SpecialConstant(special_constant) => todo!(),
    }
}
