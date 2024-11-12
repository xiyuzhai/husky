pub mod special_constant;

use self::special_constant::VdZfcSpecialConstant;
use super::*;

#[salsa::derive_debug_with_db]
#[salsa::as_id]
#[salsa::deref_id]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VdZfcLiteral(VdZfcTermId);

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum VdZfcLiteralData {
    NaturalNumber(String),
    NegativeInteger(String),
    FiniteDecimalRepresentation(String),
    SpecialConstant(VdZfcSpecialConstant),
}

impl VdZfcLiteral {
    pub fn data(self, db: &::salsa::Db) -> &VdZfcLiteralData {
        match self.0.data(db) {
            VdZfcTermData::Literal(data) => data,
            _ => unreachable!(),
        }
    }

    pub fn new(data: VdZfcLiteralData, db: &::salsa::Db) -> Self {
        #[cfg(test)]
        {
            match data {
                VdZfcLiteralData::NaturalNumber(ref n) => {
                    debug_assert!(!n.is_empty());
                    debug_assert!(n.chars().all(|c| c.is_digit(10)));
                }
                VdZfcLiteralData::NegativeInteger(_) => todo!(),
                VdZfcLiteralData::FiniteDecimalRepresentation(_) => todo!(),
                VdZfcLiteralData::SpecialConstant(vd_zfc_special_constant) => todo!(),
            }
        }
        Self(VdZfcTermId::new(db, data.into()))
    }
}

impl VdZfcLiteralData {
    pub fn as_str(&self) -> &str {
        match self {
            VdZfcLiteralData::NaturalNumber(n) => n,
            VdZfcLiteralData::NegativeInteger(n) => n,
            VdZfcLiteralData::FiniteDecimalRepresentation(n) => n,
            VdZfcLiteralData::SpecialConstant(_) => {
                todo!()
            }
        }
    }
}
