mod option;
pub mod owned;
mod primitive;
mod ritchie;
mod static_ref;
mod tuple;
mod vec;

use self::owned::*;
use crate::exception::Excepted;
use crate::{
    slush::{SlushValue, SlushValues},
    thawed::{Thawed, ThawedDyn},
    *,
};
use frozen::{Frozen, FrozenDyn, FrozenValue};
use husky_decl_macro_utils::*;
#[cfg(feature = "constant")]
use husky_term_prelude::literal::StringLiteralTokenData;
use husky_value::ki_control_flow::KiControlFlow;
use husky_value::IsValue;
use husky_value_macros::value_ty;
use husky_value_protocol::presentation::{
    synchrotron::ValuePresentationSynchrotron, EnumUnitValuePresenter, ValuePresentation,
    ValuePresenterCache,
};
use husky_visual_protocol::{
    synchrotron::VisualSynchrotron,
    visual::{primitive::PrimitiveVisual, Visual},
};
use ordered_float::OrderedFloat;
use serde::Serialize;
use std::cmp::Ordering;
use thawed::{FromThawedValue, ThawedValue};

pub(crate) const REGULAR_VALUE_SIZE_OVER_I64: usize = 4;

/// we use this layout instead of struct to reduce size to `2 * std::mem::size_of::<usize>()`
#[value_ty]
#[derive(Debug)]
#[repr(u8)]
pub enum Value {
    Unit(()),
    Bool(bool),
    Char(char),
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    I128(i128),
    ISize(isize),
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    U128(u128),
    USize(usize),
    R8(u8),
    R16(u16),
    R32(u32),
    R64(u64),
    R128(u128),
    RSize(usize),
    F32(OrderedFloat<f32>),
    F64(OrderedFloat<f64>),
    StringLiteral(StringLiteralId),
    /// `Box<T>`
    Owned(OwnedValue),
    // ad hoc
    /// `~T`
    Leash(&'static dyn ImmortalDyn),
    OptionBox(Option<Box<dyn ImmortalDyn>>),
    OptionLeash(Option<&'static dyn ImmortalDyn>),
    EnumUnit {
        index: usize,
        presenter: EnumUnitValuePresenter,
    },
}

impl Eq for Value {}

pub trait Immortal:
    Thawed<Frozen = Self>
    + Frozen<Thawed = Self>
    + FromValue
    + IntoValue
    + std::any::Any
    + RefUnwindSafe
    + UnwindSafe
    + Send
    + Sync
    + 'static
{
    /// copy if the type is copyable
    ///
    /// note that it should always be either some or none for a fixed type
    fn try_copy(&self) -> Option<Value>;

    fn index_owned(self, index: usize) -> ExceptedValue {
        panic!(
            "type `{}` doesn't support indexing owned",
            std::any::type_name::<Self>()
        )
    }

    fn index_ref<'a>(&'a self, index: usize) -> ExceptedValue {
        panic!(
            "type `{}` doesn't support indexing ref",
            std::any::type_name::<Self>()
        )
    }

    fn index_leash(&'static self, index: usize) -> ExceptedValue {
        panic!(
            "type `{}` doesn't support indexing leash",
            std::any::type_name::<Self>()
        )
    }

    fn unwrap_leash(&'static self) -> ExceptedValue {
        panic!(
            "type `{}` doesn't support unwrap",
            std::any::type_name::<Self>()
        )
    }
}

pub trait ImmortalDyn:
    ThawedDyn + FrozenDyn + std::any::Any + RefUnwindSafe + UnwindSafe + Send + Sync + 'static
{
    fn index_owned_dyn(self: Box<Self>, index: usize) -> ExceptedValue;
    fn index_leash_dyn(&'static self, index: usize) -> ExceptedValue;
    fn try_copy_dyn(&self) -> Option<Value>;
    fn unwrap_leash_dyn(&'static self) -> ExceptedValue;
}

impl<T> ImmortalDyn for T
where
    T: Immortal,
{
    fn try_copy_dyn(&self) -> Option<Value> {
        self.try_copy()
    }

    fn unwrap_leash_dyn(&'static self) -> ExceptedValue {
        self.unwrap_leash()
    }

    fn index_owned_dyn(self: Box<Self>, index: usize) -> ExceptedValue {
        (*self).index_owned(index)
    }

    fn index_leash_dyn(&'static self, index: usize) -> ExceptedValue {
        self.index_leash(index)
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct StringLiteralId(NonZeroU32);

#[cfg(feature = "constant")]
impl From<StringLiteralTokenData> for StringLiteralId {
    fn from(lit: StringLiteralTokenData) -> Self {
        unsafe { std::mem::transmute(lit) }
    }
}

#[test]
fn regular_value_size_works() {
    assert_eq!(
        std::mem::size_of::<Value>(),
        std::mem::size_of::<[u64; REGULAR_VALUE_SIZE_OVER_I64]>()
    )
}

impl From<std::convert::Infallible> for Value {
    fn from(_: std::convert::Infallible) -> Self {
        unreachable!()
    }
}

impl Value {
    pub fn from_owned<T>(t: T) -> Self
    where
        T: Immortal,
    {
        Value::Owned(OwnedValue::upcast_from_owned(t))
    }

    pub fn into_owned<T>(self) -> T
    where
        T: 'static,
    {
        match self {
            Value::Owned(slf) => slf.downcast_into_owned(),
            // ad hoc
            Value::Leash(slf) => slf.try_copy_dyn().unwrap().into_owned(),
            // *(slf.try_copy_dyn() as Box<dyn std::any::Any>)
            //     .downcast()
            //     .unwrap(),
            _ => unreachable!("self is {self:?}"),
        }
    }

    pub fn from_leash<T>(t: &'static T) -> Self
    where
        T: ImmortalDyn,
    {
        Value::Leash(t)
    }

    pub fn into_leash<T>(self) -> &'static T {
        match self {
            // ad hoc, we maybe encounter &'static Leash<T> here, so can't always just unwrap it
            Value::Leash(slf) => (slf as &dyn std::any::Any).downcast_ref().unwrap(),
            _ => unreachable!(),
        }
    }

    pub fn from_enum_index(index: usize, presenter: EnumUnitValuePresenter) -> Self {
        Value::EnumUnit { index, presenter }
    }

    pub fn into_ref<'a, T>(self, slush_values: Option<&mut SlushValues>) -> &'a T
    where
        T: Immortal,
    {
        match self {
            Value::Unit(_) => todo!(),
            Value::Bool(_) => todo!(),
            Value::Char(_) => todo!(),
            Value::I8(_) => todo!(),
            Value::I16(_) => todo!(),
            Value::I32(_) => todo!(),
            Value::I64(_) => todo!(),
            Value::I128(_) => todo!(),
            Value::ISize(_) => todo!(),
            Value::U8(_) => todo!(),
            Value::U16(_) => todo!(),
            Value::U32(_) => todo!(),
            Value::U64(_) => todo!(),
            Value::U128(_) => todo!(),
            Value::USize(_) => todo!(),
            Value::R8(_) => todo!(),
            Value::R16(_) => todo!(),
            Value::R32(_) => todo!(),
            Value::R64(_) => todo!(),
            Value::R128(_) => todo!(),
            Value::RSize(_) => todo!(),
            Value::F32(_) => todo!(),
            Value::F64(_) => todo!(),
            Value::StringLiteral(_) => todo!(),
            Value::Owned(slf) => {
                // todo: make the whole function unsafe
                let t: &T = slf.downcast_as_ref();
                let t = unsafe { std::mem::transmute(t) };
                slush_values
                    .unwrap()
                    .push(SlushValue::Box(slf.into_inner()));
                t
            }
            Value::Leash(slf) => {
                let slf: &T = ((slf as &dyn ImmortalDyn) as &dyn std::any::Any)
                    .downcast_ref()
                    .expect("type id is correct");
                unsafe { std::mem::transmute(slf) }
            }
            Value::OptionBox(_) => todo!(),
            Value::OptionLeash(_) => todo!(),
            Value::EnumUnit { .. } => todo!(),
        }
    }
}

impl IsValue for Value {
    type Exception = Exception;

    fn from_r8(r: u8) -> Self {
        Value::R8(r)
    }

    fn from_r16(r: u16) -> Self {
        Value::R16(r)
    }

    fn from_r32(r: u32) -> Self {
        Value::R32(r)
    }

    fn from_r64(r: u64) -> Self {
        Value::R64(r)
    }

    fn from_r128(r: u128) -> Self {
        Value::R128(r)
    }

    fn from_rsize(r: u64) -> Self {
        Value::RSize(r as usize)
    }

    fn from_enum_index(index: usize, presenter: EnumUnitValuePresenter) -> Self {
        Value::EnumUnit { index, presenter }
    }

    fn share(&'static self) -> Self {
        match *self {
            Value::Unit(slf) => Value::Unit(slf),
            Value::Bool(slf) => Value::Bool(slf),
            Value::Char(slf) => Value::Char(slf),
            Value::I8(slf) => Value::I8(slf),
            Value::I16(slf) => Value::I16(slf),
            Value::I32(slf) => Value::I32(slf),
            Value::I64(slf) => Value::I64(slf),
            Value::I128(slf) => Value::I128(slf),
            Value::ISize(slf) => Value::ISize(slf),
            Value::U8(slf) => Value::U8(slf),
            Value::U16(slf) => Value::U16(slf),
            Value::U32(slf) => Value::U32(slf),
            Value::U64(slf) => Value::U64(slf),
            Value::U128(slf) => Value::U128(slf),
            Value::USize(slf) => Value::USize(slf),
            Value::R8(slf) => Value::R8(slf),
            Value::R16(slf) => Value::R16(slf),
            Value::R32(slf) => Value::R32(slf),
            Value::R64(slf) => Value::R64(slf),
            Value::R128(slf) => Value::R128(slf),
            Value::RSize(slf) => Value::RSize(slf),
            Value::F32(slf) => Value::F32(slf),
            Value::F64(slf) => Value::F64(slf),
            Value::StringLiteral(slf) => Value::StringLiteral(slf),
            Value::Owned(ref slf) => Value::Leash(slf.as_ref()), // Clone the boxed value
            Value::Leash(slf) => Value::Leash(slf),
            Value::OptionBox(ref slf) => Value::OptionLeash(slf.as_ref().map(|v| &**v)), // Clone the boxed option
            Value::OptionLeash(slf) => Value::OptionLeash(slf),
            Value::EnumUnit { index, presenter } => Value::EnumUnit { index, presenter },
        }
    }

    fn to_bool(self) -> bool {
        match self {
            Value::Bool(val) => val,
            Value::Char(val) => val != Default::default(),
            Value::I8(val) => val != 0,
            Value::I16(val) => val != 0,
            Value::I32(val) => val != 0,
            Value::I64(val) => val != 0,
            Value::I128(val) => val != 0,
            Value::ISize(val) => val != 0,
            Value::U8(val) => val != 0,
            Value::U16(val) => val != 0,
            Value::U32(val) => val != 0,
            Value::U64(val) => val != 0,
            Value::U128(val) => val != 0,
            Value::USize(val) => val != 0,
            Value::R8(val) => val != 0,
            Value::R16(val) => val != 0,
            Value::R32(val) => val != 0,
            Value::R64(val) => val != 0,
            Value::R128(val) => val != 0,
            Value::RSize(val) => val != 0,
            _ => unreachable!(),
        }
    }

    fn is_none(self) -> bool {
        match self {
            Value::OptionBox(opt) => opt.is_none(),
            Value::OptionLeash(opt) => opt.is_none(),
            Value::Leash(opt) => opt.is_none_dyn(),
            _ => {
                unreachable!()
            }
        }
    }

    fn is_some(self) -> bool {
        match self {
            Value::OptionBox(opt) => opt.is_some(),
            Value::OptionLeash(opt) => opt.is_some(),
            Value::Leash(opt) => opt.is_some_dyn(),
            _ => unreachable!(),
        }
    }

    fn to_usize(self) -> usize {
        match self {
            Value::I8(slf) => slf as usize,
            Value::I16(slf) => slf as usize,
            Value::I32(slf) => slf as usize,
            Value::I64(slf) => slf as usize,
            Value::I128(slf) => slf as usize,
            Value::ISize(slf) => slf as usize,
            Value::U8(slf) => slf as usize,
            Value::U16(slf) => slf as usize,
            Value::U32(slf) => slf as usize,
            Value::U64(slf) => slf as usize,
            Value::U128(slf) => slf as usize,
            Value::USize(slf) => slf,
            Value::R8(slf) => slf as usize,
            Value::R16(slf) => slf as usize,
            Value::R32(slf) => slf as usize,
            Value::R64(slf) => slf as usize,
            Value::R128(slf) => slf as usize,
            Value::RSize(slf) => slf as usize,
            Value::EnumUnit { .. } => todo!(),
            _ => unreachable!(),
        }
    }

    fn index(self, index: usize) -> Excepted<Self> {
        match self {
            Value::Unit(_) => todo!(),
            Value::Bool(_) => todo!(),
            Value::Char(_) => todo!(),
            Value::I8(_) => todo!(),
            Value::I16(_) => todo!(),
            Value::I32(_) => todo!(),
            Value::I64(_) => todo!(),
            Value::I128(_) => todo!(),
            Value::ISize(_) => todo!(),
            Value::U8(_) => todo!(),
            Value::U16(_) => todo!(),
            Value::U32(_) => todo!(),
            Value::U64(_) => todo!(),
            Value::U128(_) => todo!(),
            Value::USize(_) => todo!(),
            Value::R8(_) => todo!(),
            Value::R16(_) => todo!(),
            Value::R32(_) => todo!(),
            Value::R64(_) => todo!(),
            Value::R128(_) => todo!(),
            Value::RSize(_) => todo!(),
            Value::F32(_) => todo!(),
            Value::F64(_) => todo!(),
            Value::StringLiteral(_) => todo!(),
            Value::Owned(slf) => slf.index_owned_dyn(index),
            Value::Leash(slf) => slf.index_leash_dyn(index),
            Value::OptionBox(_) => todo!(),
            Value::OptionLeash(_) => todo!(),
            Value::EnumUnit { .. } => todo!(),
        }
    }

    fn present(
        &self,
        cache: &mut ValuePresenterCache,
        value_presentation_synchrotron: &mut ValuePresentationSynchrotron,
    ) -> ValuePresentation {
        match *self {
            Value::Unit(_) => ValuePresentation::Unit(()),
            Value::Bool(b) => ValuePresentation::Bool(b),
            Value::Char(c) => ValuePresentation::Char(c),
            Value::I8(i) => ValuePresentation::I8(i),
            Value::I16(i) => ValuePresentation::I16(i),
            Value::I32(i) => ValuePresentation::I32(i),
            Value::I64(i) => ValuePresentation::I64(i),
            Value::I128(i) => ValuePresentation::I128(i),
            Value::ISize(i) => ValuePresentation::ISize(i),
            Value::U8(u) => ValuePresentation::U8(u),
            Value::U16(u) => ValuePresentation::U16(u),
            Value::U32(u) => ValuePresentation::U32(u),
            Value::U64(u) => ValuePresentation::U64(u),
            Value::U128(u) => ValuePresentation::U128(u),
            Value::USize(u) => ValuePresentation::USize(u),
            Value::R8(r) => ValuePresentation::R8(r),
            Value::R16(r) => ValuePresentation::R16(r),
            Value::R32(r) => ValuePresentation::R32(r),
            Value::R64(r) => ValuePresentation::R64(r),
            Value::R128(r) => ValuePresentation::R128(r),
            Value::RSize(r) => ValuePresentation::RSize(r),
            Value::F32(f) => ValuePresentation::F32(f.into()),
            Value::F64(f) => ValuePresentation::F64(f.into()),
            Value::StringLiteral(_) => todo!(),
            Value::Owned(ref value) => (**value).present_dyn(),
            Value::Leash(value) => value.present_dyn(),
            Value::OptionBox(ref value) => todo!(),
            Value::OptionLeash(_) => todo!(),
            Value::EnumUnit { index, presenter } => {
                presenter(index, cache, value_presentation_synchrotron)
            }
        }
    }

    fn visualize(&self, visual_synchrotron: &mut VisualSynchrotron) -> Visual {
        use husky_visual_protocol::visualize::Visualize;
        match *self {
            Value::Unit(_) => Visual::Void,
            Value::Bool(_) => todo!(),
            Value::Char(_) => todo!(),
            Value::I8(value) => PrimitiveVisual::I8(value).into(),
            Value::I16(_) => todo!(),
            Value::I32(_) => todo!(),
            Value::I64(_) => todo!(),
            Value::I128(_) => todo!(),
            Value::ISize(_) => todo!(),
            Value::U8(_) => todo!(),
            Value::U16(_) => todo!(),
            Value::U32(_) => todo!(),
            Value::U64(_) => todo!(),
            Value::U128(_) => todo!(),
            Value::USize(_) => todo!(),
            Value::R8(_) => todo!(),
            Value::R16(_) => todo!(),
            Value::R32(_) => todo!(),
            Value::R64(_) => todo!(),
            Value::R128(_) => todo!(),
            Value::RSize(_) => todo!(),
            Value::F32(f) => f.visualize(visual_synchrotron),
            Value::F64(_) => todo!(),
            Value::StringLiteral(_) => todo!(),
            Value::Owned(ref value) => (**value).visualize_or_void_dyn(visual_synchrotron),
            Value::Leash(value) => value.visualize_or_void_dyn(visual_synchrotron),
            Value::OptionBox(_) => todo!(),
            Value::OptionLeash(_) => todo!(),
            Value::EnumUnit { .. } => Visual::Void,
        }
    }

    fn from_str_literal(str_value: Arc<str>) -> Self {
        todo!()
    }

    fn unwrap(self) -> ExceptedValue {
        match self {
            Value::Unit(_) => todo!(),
            Value::Bool(_) => todo!(),
            Value::Char(_) => todo!(),
            Value::I8(_) => todo!(),
            Value::I16(_) => todo!(),
            Value::I32(_) => todo!(),
            Value::I64(_) => todo!(),
            Value::I128(_) => todo!(),
            Value::ISize(_) => todo!(),
            Value::U8(_) => todo!(),
            Value::U16(_) => todo!(),
            Value::U32(_) => todo!(),
            Value::U64(_) => todo!(),
            Value::U128(_) => todo!(),
            Value::USize(_) => todo!(),
            Value::R8(_) => todo!(),
            Value::R16(_) => todo!(),
            Value::R32(_) => todo!(),
            Value::R64(_) => todo!(),
            Value::R128(_) => todo!(),
            Value::RSize(_) => todo!(),
            Value::F32(_) => todo!(),
            Value::F64(_) => todo!(),
            Value::StringLiteral(_) => todo!(),
            Value::Owned(_) => todo!(),
            Value::Leash(slf) => slf.unwrap_leash_dyn(),
            Value::OptionBox(_) => todo!(),
            Value::OptionLeash(_) => todo!(),
            Value::EnumUnit { index, presenter } => todo!(),
        }
    }

    type FrozenValue = FrozenValue;

    type SlushValue = SlushValue;

    type ThawedValue = ThawedValue;
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Unit(l0), Self::Unit(r0)) => l0 == r0,
            (Self::Bool(l0), Self::Bool(r0)) => l0 == r0,
            (Self::Char(l0), Self::Char(r0)) => l0 == r0,
            (Self::I8(l0), Self::I8(r0)) => l0 == r0,
            (Self::I16(l0), Self::I16(r0)) => l0 == r0,
            (Self::I32(l0), Self::I32(r0)) => l0 == r0,
            (Self::I64(l0), Self::I64(r0)) => l0 == r0,
            (Self::I128(l0), Self::I128(r0)) => l0 == r0,
            (Self::ISize(l0), Self::ISize(r0)) => l0 == r0,
            (Self::U8(l0), Self::U8(r0)) => l0 == r0,
            (Self::U16(l0), Self::U16(r0)) => l0 == r0,
            (Self::U32(l0), Self::U32(r0)) => l0 == r0,
            (Self::U64(l0), Self::U64(r0)) => l0 == r0,
            (Self::U128(l0), Self::U128(r0)) => l0 == r0,
            (Self::USize(l0), Self::USize(r0)) => l0 == r0,
            (Self::R8(l0), Self::R8(r0)) => l0 == r0,
            (Self::R16(l0), Self::R16(r0)) => l0 == r0,
            (Self::R32(l0), Self::R32(r0)) => l0 == r0,
            (Self::R64(l0), Self::R64(r0)) => l0 == r0,
            (Self::R128(l0), Self::R128(r0)) => l0 == r0,
            (Self::RSize(l0), Self::RSize(r0)) => l0 == r0,
            (Self::F32(l0), Self::F32(r0)) => l0 == r0,
            (Self::F64(l0), Self::F64(r0)) => l0 == r0,
            (Self::StringLiteral(l0), Self::StringLiteral(r0)) => todo!(),
            (Self::Owned(l0), Self::Owned(r0)) => todo!(),
            (Self::Leash(l0), Self::Leash(r0)) => todo!(),
            (Self::OptionBox(l0), Self::OptionBox(r0)) => todo!(),
            (Self::OptionLeash(l0), Self::OptionLeash(r0)) => todo!(),
            (Self::EnumUnit { index: l0, .. }, Self::EnumUnit { index: r0, .. }) => l0 == r0,
            _ => unreachable!(),
        }
    }
}

impl PartialOrd for Value {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        use Value::*;
        match (self, other) {
            (Unit(_), Unit(_)) => Some(Ordering::Equal),
            (Bool(b1), Bool(b2)) => b1.partial_cmp(b2),
            (Char(c1), Char(c2)) => c1.partial_cmp(c2),
            (I8(i1), I8(i2)) => i1.partial_cmp(i2),
            (I16(i1), I16(i2)) => i1.partial_cmp(i2),
            (I32(i1), I32(i2)) => i1.partial_cmp(i2),
            (I64(i1), I64(i2)) => i1.partial_cmp(i2),
            (I128(i1), I128(i2)) => i1.partial_cmp(i2),
            (ISize(i1), ISize(i2)) => i1.partial_cmp(i2),
            (U8(u1), U8(u2)) => u1.partial_cmp(u2),
            (U16(u1), U16(u2)) => u1.partial_cmp(u2),
            (U32(u1), U32(u2)) => u1.partial_cmp(u2),
            (U64(u1), U64(u2)) => u1.partial_cmp(u2),
            (U128(u1), U128(u2)) => u1.partial_cmp(u2),
            (USize(u1), USize(u2)) => u1.partial_cmp(u2),
            (F32(f1), F32(f2)) => f1.partial_cmp(f2),
            (F64(f1), F64(f2)) => f1.partial_cmp(f2),
            (StringLiteral(l0), StringLiteral(r0)) => todo!(),
            (Value::Owned(l0), Value::Owned(r0)) => todo!(),
            (Leash(l0), Leash(r0)) => todo!(),
            (OptionBox(l0), OptionBox(r0)) => todo!(),
            (OptionLeash(l0), OptionLeash(r0)) => todo!(),
            (EnumUnit { index: l0, .. }, EnumUnit { index: r0, .. }) => todo!(),
            _ => unreachable!(),
        }
    }
}

impl std::ops::Add<Value> for Value {
    type Output = Self;

    fn add(self, rhs: Value) -> Self::Output {
        match (self, rhs) {
            (Value::I8(a), Value::I8(b)) => Value::I8(a + b),
            (Value::I16(a), Value::I16(b)) => Value::I16(a + b),
            (Value::I32(a), Value::I32(b)) => Value::I32(a + b),
            (Value::I64(a), Value::I64(b)) => Value::I64(a + b),
            (Value::I128(a), Value::I128(b)) => Value::I128(a + b),
            (Value::ISize(a), Value::ISize(b)) => Value::ISize(a + b),
            (Value::U8(a), Value::U8(b)) => Value::U8(a + b),
            (Value::U16(a), Value::U16(b)) => Value::U16(a + b),
            (Value::U32(a), Value::U32(b)) => Value::U32(a + b),
            (Value::U64(a), Value::U64(b)) => Value::U64(a + b),
            (Value::U128(a), Value::U128(b)) => Value::U128(a + b),
            (Value::USize(a), Value::USize(b)) => Value::USize(a + b),
            (Value::R8(a), Value::R8(b)) => Value::R8(a + b),
            (Value::R16(a), Value::R16(b)) => Value::R16(a + b),
            (Value::R32(a), Value::R32(b)) => Value::R32(a + b),
            (Value::R64(a), Value::R64(b)) => Value::R64(a + b),
            (Value::R128(a), Value::R128(b)) => Value::R128(a + b),
            (Value::RSize(a), Value::RSize(b)) => Value::RSize(a + b),
            (Value::F32(a), Value::F32(b)) => Value::F32(a + b),
            (Value::F64(a), Value::F64(b)) => Value::F64(a + b),
            _ => unreachable!(),
        }
    }
}

impl std::ops::AddAssign<Value> for Value {
    fn add_assign(&mut self, rhs: Value) {
        todo!()
    }
}

impl std::ops::BitAnd for Value {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::R8(a), Value::R8(b)) => Value::R8(a & b),
            (Value::R16(a), Value::R16(b)) => Value::R16(a & b),
            (Value::R32(a), Value::R32(b)) => Value::R32(a & b),
            (Value::R64(a), Value::R64(b)) => Value::R64(a & b),
            (Value::R128(a), Value::R128(b)) => Value::R128(a & b),
            (Value::RSize(a), Value::RSize(b)) => Value::RSize(a & b),
            _ => unreachable!(),
        }
    }
}

impl std::ops::BitAndAssign for Value {
    fn bitand_assign(&mut self, rhs: Self) {
        todo!()
    }
}

impl std::ops::BitOr for Value {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::R8(a), Value::R8(b)) => Value::R8(a | b),
            (Value::R16(a), Value::R16(b)) => Value::R16(a | b),
            (Value::R32(a), Value::R32(b)) => Value::R32(a | b),
            (Value::R64(a), Value::R64(b)) => Value::R64(a | b),
            (Value::R128(a), Value::R128(b)) => Value::R128(a | b),
            (Value::RSize(a), Value::RSize(b)) => Value::RSize(a | b),
            _ => unreachable!(),
        }
    }
}

impl std::ops::BitOrAssign for Value {
    fn bitor_assign(&mut self, rhs: Self) {
        todo!()
    }
}

impl std::ops::BitXor for Value {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        todo!()
    }
}

impl std::ops::BitXorAssign for Value {
    fn bitxor_assign(&mut self, rhs: Self) {
        todo!()
    }
}

impl std::ops::Div for Value {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::I8(a), Value::I8(b)) => Value::I8(a / b),
            (Value::I16(a), Value::I16(b)) => Value::I16(a / b),
            (Value::I32(a), Value::I32(b)) => Value::I32(a / b),
            (Value::I64(a), Value::I64(b)) => Value::I64(a / b),
            (Value::I128(a), Value::I128(b)) => Value::I128(a / b),
            (Value::ISize(a), Value::ISize(b)) => Value::ISize(a / b),
            (Value::U8(a), Value::U8(b)) => Value::U8(a / b),
            (Value::U16(a), Value::U16(b)) => Value::U16(a / b),
            (Value::U32(a), Value::U32(b)) => Value::U32(a / b),
            (Value::U64(a), Value::U64(b)) => Value::U64(a / b),
            (Value::U128(a), Value::U128(b)) => Value::U128(a / b),
            (Value::USize(a), Value::USize(b)) => Value::USize(a / b),
            (Value::R8(a), Value::R8(b)) => Value::R8(a / b),
            (Value::R16(a), Value::R16(b)) => Value::R16(a / b),
            (Value::R32(a), Value::R32(b)) => Value::R32(a / b),
            (Value::R64(a), Value::R64(b)) => Value::R64(a / b),
            (Value::R128(a), Value::R128(b)) => Value::R128(a / b),
            (Value::RSize(a), Value::RSize(b)) => Value::RSize(a / b),
            (Value::F32(a), Value::F32(b)) => Value::F32(a / b),
            (Value::F64(a), Value::F64(b)) => Value::F64(a / b),
            _ => unreachable!(),
        }
    }
}

impl std::ops::Mul for Value {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::I8(a), Value::I8(b)) => Value::I8(a * b),
            (Value::I16(a), Value::I16(b)) => Value::I16(a * b),
            (Value::I32(a), Value::I32(b)) => Value::I32(a * b),
            (Value::I64(a), Value::I64(b)) => Value::I64(a * b),
            (Value::I128(a), Value::I128(b)) => Value::I128(a * b),
            (Value::ISize(a), Value::ISize(b)) => Value::ISize(a * b),
            (Value::U8(a), Value::U8(b)) => Value::U8(a * b),
            (Value::U16(a), Value::U16(b)) => Value::U16(a * b),
            (Value::U32(a), Value::U32(b)) => Value::U32(a * b),
            (Value::U64(a), Value::U64(b)) => Value::U64(a * b),
            (Value::U128(a), Value::U128(b)) => Value::U128(a * b),
            (Value::USize(a), Value::USize(b)) => Value::USize(a * b),
            (Value::R8(a), Value::R8(b)) => Value::R8(a * b),
            (Value::R16(a), Value::R16(b)) => Value::R16(a * b),
            (Value::R32(a), Value::R32(b)) => Value::R32(a * b),
            (Value::R64(a), Value::R64(b)) => Value::R64(a * b),
            (Value::R128(a), Value::R128(b)) => Value::R128(a * b),
            (Value::RSize(a), Value::RSize(b)) => Value::RSize(a * b),
            (Value::F32(a), Value::F32(b)) => Value::F32(a * b),
            (Value::F64(a), Value::F64(b)) => Value::F64(a * b),
            _ => unreachable!(),
        }
    }
}

impl std::ops::MulAssign for Value {
    fn mul_assign(&mut self, rhs: Self) {
        todo!()
    }
}

impl std::ops::Neg for Value {
    type Output = Self;

    fn neg(self) -> Self::Output {
        match self {
            Value::Unit(_) => todo!(),
            Value::Bool(_) => todo!(),
            Value::Char(_) => todo!(),
            Value::I8(i) => Value::I8(-i),
            Value::I16(i) => Value::I16(-i),
            Value::I32(i) => Value::I32(-i),
            Value::I64(i) => Value::I64(-i),
            Value::I128(i) => Value::I128(-i),
            Value::ISize(i) => Value::ISize(-i),
            Value::U8(_) => todo!(),
            Value::U16(_) => todo!(),
            Value::U32(_) => todo!(),
            Value::U64(_) => todo!(),
            Value::U128(_) => todo!(),
            Value::USize(_) => todo!(),
            Value::R8(_) => todo!(),
            Value::R16(_) => todo!(),
            Value::R32(_) => todo!(),
            Value::R64(_) => todo!(),
            Value::R128(_) => todo!(),
            Value::RSize(_) => todo!(),
            Value::F32(f) => Value::F32(-f),
            Value::F64(f) => Value::F64(-f),
            Value::StringLiteral(_) => todo!(),
            Value::Owned(_) => todo!(),
            Value::Leash(_) => todo!(),
            Value::OptionBox(_) => todo!(),
            Value::OptionLeash(_) => todo!(),
            Value::EnumUnit { index, presenter } => todo!(),
        }
    }
}

impl std::ops::Not for Value {
    type Output = Self;

    fn not(self) -> Self::Output {
        todo!()
    }
}

impl std::ops::Shl for Value {
    type Output = Self;

    fn shl(self, rhs: Self) -> Self::Output {
        todo!()
    }
}

impl std::ops::ShlAssign for Value {
    fn shl_assign(&mut self, rhs: Self) {
        todo!()
    }
}

impl std::ops::Shr for Value {
    type Output = Self;

    fn shr(self, rhs: Self) -> Self::Output {
        todo!()
    }
}

impl std::ops::ShrAssign for Value {
    fn shr_assign(&mut self, rhs: Self) {
        todo!()
    }
}

impl std::ops::Sub for Value {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (Value::I8(a), Value::I8(b)) => Value::I8(a - b),
            (Value::I16(a), Value::I16(b)) => Value::I16(a - b),
            (Value::I32(a), Value::I32(b)) => Value::I32(a - b),
            (Value::I64(a), Value::I64(b)) => Value::I64(a - b),
            (Value::I128(a), Value::I128(b)) => Value::I128(a - b),
            (Value::ISize(a), Value::ISize(b)) => Value::ISize(a - b),
            (Value::U8(a), Value::U8(b)) => Value::U8(a - b),
            (Value::U16(a), Value::U16(b)) => Value::U16(a - b),
            (Value::U32(a), Value::U32(b)) => Value::U32(a - b),
            (Value::U64(a), Value::U64(b)) => Value::U64(a - b),
            (Value::U128(a), Value::U128(b)) => Value::U128(a - b),
            (Value::USize(a), Value::USize(b)) => Value::USize(a - b),
            (Value::R8(a), Value::R8(b)) => Value::R8(a - b),
            (Value::R16(a), Value::R16(b)) => Value::R16(a - b),
            (Value::R32(a), Value::R32(b)) => Value::R32(a - b),
            (Value::R64(a), Value::R64(b)) => Value::R64(a - b),
            (Value::R128(a), Value::R128(b)) => Value::R128(a - b),
            (Value::RSize(a), Value::RSize(b)) => Value::RSize(a - b),
            (Value::F32(a), Value::F32(b)) => Value::F32(a - b),
            (Value::F64(a), Value::F64(b)) => Value::F64(a - b),
            _ => unreachable!(),
        }
    }
}

impl std::ops::SubAssign for Value {
    fn sub_assign(&mut self, rhs: Self) {
        todo!()
    }
}
