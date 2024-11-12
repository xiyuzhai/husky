use crate::*;
use husky_hir_prelude::HirLiteral;
use ordered_float::OrderedFloat;

/// precompiled to save conversion
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct __RegularValueConstant([u64; REGULAR_VALUE_SIZE_OVER_I64]);

impl __RegularValueConstant {
    // change to HirConstant instead
    pub fn new(constant: HirLiteral, _db: &::salsa::Db) -> Self {
        let value: Value = match constant {
            HirLiteral::Unit(()) => Value::Unit(()),
            HirLiteral::Bool(v) => Value::Bool(v),
            HirLiteral::Char(v) => Value::Char(v),
            HirLiteral::I8(v) => Value::I8(v),
            HirLiteral::I16(v) => Value::I16(v),
            HirLiteral::I32(v) => Value::I32(v),
            HirLiteral::I64(v) => Value::I64(v),
            HirLiteral::I128(v) => Value::I128(v),
            HirLiteral::ISize(v) => Value::ISize(v),
            HirLiteral::U8(v) => Value::U8(v),
            HirLiteral::U16(v) => Value::U16(v),
            HirLiteral::U32(v) => Value::U32(v),
            HirLiteral::U64(v) => Value::U64(v),
            HirLiteral::U128(v) => Value::U128(v),
            HirLiteral::USize(v) => Value::USize(v),
            HirLiteral::R8(v) => Value::R8(v),
            HirLiteral::R16(v) => Value::R16(v),
            HirLiteral::R32(v) => Value::R32(v),
            HirLiteral::R64(v) => Value::R64(v),
            HirLiteral::R128(v) => Value::R128(v),
            HirLiteral::RSize(v) => Value::RSize(v),
            HirLiteral::F32(v) => Value::F32(OrderedFloat(v.into_inner())),
            HirLiteral::F64(v) => Value::F64(OrderedFloat(v.into_inner())),
            HirLiteral::StringLiteral(v) => Value::StringLiteral(v.into()),
        };
        Self(unsafe { std::mem::transmute(value) })
    }
}

impl From<__RegularValueConstant> for Value {
    fn from(constant: __RegularValueConstant) -> Self {
        unsafe { std::mem::transmute(constant.0) }
    }
}
