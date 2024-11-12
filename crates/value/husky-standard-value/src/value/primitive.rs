use super::*;

macro_rules! impl_thawed_for_primitive_ty {
    ($primitive_ty: ty) => {
        impl Immortal for $primitive_ty {
            fn try_copy(&self) -> Option<Value> {
                Some((*self).into())
            }
        }
    };
}

for_all_primitive_tys!(impl_thawed_for_primitive_ty);

impl From<()> for Value {
    fn from(value: ()) -> Self {
        Value::Unit(())
    }
}

impl Into<()> for Value {
    fn into(self) -> () {
        match self {
            Value::Unit(()) => (),
            _ => {
                println!("self = {:?}", self);
                unreachable!()
            }
        }
    }
}

impl From<bool> for Value {
    fn from(value: bool) -> Self {
        Value::Bool(value)
    }
}

impl Into<bool> for Value {
    fn into(self) -> bool {
        match self {
            Value::Bool(value) => value,
            _ => unreachable!(),
        }
    }
}

impl From<u8> for Value {
    fn from(value: u8) -> Self {
        Value::U8(value)
    }
}

impl Into<u8> for Value {
    fn into(self) -> u8 {
        match self {
            Value::U8(value) => value,
            _ => unreachable!(),
        }
    }
}

impl From<u16> for Value {
    fn from(value: u16) -> Self {
        Value::U16(value)
    }
}

impl Into<u16> for Value {
    fn into(self) -> u16 {
        match self {
            Value::U16(value) => value,
            _ => unreachable!(),
        }
    }
}

impl From<u32> for Value {
    fn from(value: u32) -> Self {
        Value::U32(value)
    }
}

impl Into<u32> for Value {
    fn into(self) -> u32 {
        match self {
            Value::U32(value) => value,
            _ => unreachable!(),
        }
    }
}

impl From<u64> for Value {
    fn from(value: u64) -> Self {
        Value::U64(value)
    }
}

impl Into<u64> for Value {
    fn into(self) -> u64 {
        match self {
            Value::U64(value) => value,
            _ => unreachable!(),
        }
    }
}

impl From<u128> for Value {
    fn from(value: u128) -> Self {
        Value::U128(value)
    }
}

impl Into<u128> for Value {
    fn into(self) -> u128 {
        match self {
            Value::U128(value) => value,
            _ => unreachable!(),
        }
    }
}

impl From<usize> for Value {
    fn from(value: usize) -> Self {
        Value::USize(value)
    }
}

impl Into<usize> for Value {
    fn into(self) -> usize {
        match self {
            Value::USize(value) => value,
            _ => unreachable!(),
        }
    }
}

impl From<i8> for Value {
    fn from(value: i8) -> Self {
        Value::I8(value)
    }
}

impl Into<i8> for Value {
    fn into(self) -> i8 {
        match self {
            Value::I8(value) => value,
            _ => unreachable!(),
        }
    }
}

impl From<i16> for Value {
    fn from(value: i16) -> Self {
        Value::I16(value)
    }
}

impl Into<i16> for Value {
    fn into(self) -> i16 {
        match self {
            Value::I16(value) => value,
            _ => unreachable!(),
        }
    }
}

impl From<i32> for Value {
    fn from(value: i32) -> Self {
        Value::I32(value)
    }
}

impl Into<i32> for Value {
    fn into(self) -> i32 {
        match self {
            Value::I32(value) => value,
            _ => unreachable!(),
        }
    }
}

impl From<i64> for Value {
    fn from(value: i64) -> Self {
        Value::I64(value)
    }
}

impl Into<i64> for Value {
    fn into(self) -> i64 {
        match self {
            Value::I64(value) => value,
            _ => unreachable!(),
        }
    }
}

impl From<i128> for Value {
    fn from(value: i128) -> Self {
        Value::I128(value)
    }
}

impl Into<i128> for Value {
    fn into(self) -> i128 {
        match self {
            Value::I128(value) => value,
            _ => unreachable!(),
        }
    }
}

impl From<isize> for Value {
    fn from(value: isize) -> Self {
        Value::ISize(value)
    }
}

impl Into<isize> for Value {
    fn into(self) -> isize {
        match self {
            Value::ISize(value) => value,
            _ => unreachable!(),
        }
    }
}

impl From<f32> for Value {
    fn from(value: f32) -> Self {
        Value::F32(value.into())
    }
}

impl Into<f32> for Value {
    fn into(self) -> f32 {
        match self {
            Value::F32(value) => value.into(),
            _ => unreachable!(),
        }
    }
}

impl From<f64> for Value {
    fn from(value: f64) -> Self {
        Value::F64(value.into())
    }
}

impl Into<f64> for Value {
    fn into(self) -> f64 {
        match self {
            Value::F64(value) => value.into(),
            _ => unreachable!(),
        }
    }
}

impl From<char> for Value {
    fn from(value: char) -> Self {
        Value::Char(value)
    }
}

impl Into<char> for Value {
    fn into(self) -> char {
        match self {
            Value::Char(value) => value,
            _ => unreachable!(),
        }
    }
}
