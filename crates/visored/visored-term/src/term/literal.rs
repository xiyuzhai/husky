pub mod special_constant;

use self::special_constant::VdSpecialConstant;
use super::*;
use crate::{menu::vd_ty_menu, ty::VdType};

#[salsa::derive_debug_with_db]
#[salsa::as_id]
#[salsa::deref_id]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VdLiteral(VdTermId);

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum VdLiteralData {
    NaturalNumber(String),
    NegativeInteger(String),
    FiniteDecimalRepresentation(String),
    SpecialConstant(VdSpecialConstant),
}

impl VdLiteral {
    pub fn new(data: VdLiteralData, db: &::salsa::Db) -> Self {
        #[cfg(test)]
        {
            match data {
                VdLiteralData::NaturalNumber(ref n) => {
                    debug_assert!(!n.is_empty());
                    debug_assert!(n.chars().all(|c| c.is_digit(10)));
                }
                VdLiteralData::NegativeInteger(_) => todo!(),
                VdLiteralData::FiniteDecimalRepresentation(_) => todo!(),
                VdLiteralData::SpecialConstant(vd_special_constant) => todo!(),
            }
        }
        Self(VdTermId::new(db, data.into()))
    }

    pub fn data(self, db: &::salsa::Db) -> &VdLiteralData {
        match self.0.data(db) {
            VdTermData::Literal(data) => data,
            _ => unreachable!(),
        }
    }

    pub fn ty(self, db: &::salsa::Db) -> VdType {
        zfc_literal_ty(db, self)
    }
}

#[salsa::tracked]
fn zfc_literal_ty(db: &::salsa::Db, literal: VdLiteral) -> VdType {
    let data = literal.data(db);
    let menu = vd_ty_menu(db);
    match data {
        VdLiteralData::NaturalNumber(_) => menu.nat,
        VdLiteralData::NegativeInteger(_) => todo!(),
        VdLiteralData::FiniteDecimalRepresentation(_) => todo!(),
        VdLiteralData::SpecialConstant(special_constant) => todo!(),
    }
}

impl VdLiteralData {
    pub fn as_str(&self) -> &str {
        match self {
            VdLiteralData::NaturalNumber(n) => n,
            VdLiteralData::NegativeInteger(n) => n,
            VdLiteralData::FiniteDecimalRepresentation(n) => n,
            VdLiteralData::SpecialConstant(_) => {
                todo!()
            }
        }
    }
}
