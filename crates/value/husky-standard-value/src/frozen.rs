pub mod control_flow;
mod leash;
pub mod r#mut;
mod option;
mod primitive;
pub mod r#ref;
mod ritchie;
pub mod static_ref;
mod tuple;
mod vec;

use super::*;
use crate::thawed::{Thawed, ThawedDyn};
use husky_decl_macro_utils::{
    for_all_non_unit_tuple_tys, for_all_primitive_tys, for_all_ritchie_tys,
};
use husky_value::IsFrozenValue;
use husky_value_protocol::presentation::ValuePresentation;
use husky_value_protocol::presentation::{
    synchrotron::ValuePresentationSynchrotron, EnumUnitValuePresenter, ValuePresenterCache,
};
use husky_visual_protocol::visual::Visual;
use husky_visual_protocol::{synchrotron::VisualSynchrotron, visual::primitive::PrimitiveVisual};
use slush::SlushValue;
use smallvec::SmallVec;
use thawed::{FromThawedValue, ThawedValue};

pub trait Frozen:
    std::fmt::Debug + Clone + RefUnwindSafe + UnwindSafe + Send + Sync + 'static
{
    type Thawed: Thawed;
    type Slush: std::any::Any;

    /// this function gives back the value snapshoted,
    /// together with a stand so that the value is valid if the stand is not dropped.
    ///
    /// Returns None if Slush is trivial to save a call of `Box::new`.
    fn thaw(&self) -> (Option<Self::Slush>, Self::Thawed);
    fn serialize_to_value(&self) -> serde_json::Value;
    fn visualize_or_void(&self, visual_synchrotron: &mut VisualSynchrotron) -> Visual;
}

pub trait FrozenDyn: std::fmt::Debug + Send + Sync {
    /// returns a owned type and the stand it needed
    fn thaw_dyn(&self) -> (Option<SlushValue>, Box<dyn ThawedDyn>);
    fn thaw_ref_dyn(self: Arc<Self>) -> (SlushValue, *const dyn ThawedDyn);
    fn thaw_mut_dyn(&self) -> (SlushValue, *mut dyn ThawedDyn);
    fn present_dyn(&self) -> ValuePresentation;
    fn visualize_or_void_dyn(&self, visual_synchrotron: &mut VisualSynchrotron) -> Visual;
}

impl<T> FrozenDyn for T
where
    T: Frozen,
{
    fn thaw_dyn(&self) -> (Option<SlushValue>, Box<dyn ThawedDyn>) {
        let (stand, thawed_self) = self.thaw();
        (
            stand.map(|stand| SlushValue::Box(Box::<T::Slush>::new(stand))),
            Box::<T::Thawed>::new(thawed_self),
        )
    }

    fn thaw_ref_dyn(self: Arc<Self>) -> (SlushValue, *const dyn ThawedDyn) {
        todo!()
        // let slf: *const <Self as Frozen>::Thawed =
        //     unsafe { std::mem::transmute(&*self as *const Self) };
        // (SlushValue::Arc(self), slf)
    }

    fn thaw_mut_dyn(&self) -> (SlushValue, *mut dyn ThawedDyn) {
        todo!()
        // let mut slf = self.clone();
        // let slf_mut: *mut <Self as Frozen>::Thawed =
        //     unsafe { std::mem::transmute(&mut slf as *mut Self) };
        // (SlushValue::Box(Box::new(slf)), slf_mut)
    }

    fn present_dyn(&self) -> ValuePresentation {
        // self.present()
        // ad hoc
        ValuePresentation::AdHoc(format!("{self:?}"))
    }

    fn visualize_or_void_dyn(&self, visual_synchrotron: &mut VisualSynchrotron) -> Visual {
        self.visualize_or_void(visual_synchrotron)
    }
}

/// we use this layout instead of struct to reduce size to `2 * std::mem::size_of::<usize>()`
///
/// we use Arc for everything on heap to reduce clone costs
#[derive(Debug, Clone)]
#[repr(u8)]
pub enum FrozenValue {
    Uninit,
    Invalid,
    Moved,
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
    F32(f32),
    F64(f64),
    StringLiteral(StringLiteralId),
    EnumUsize {
        index: usize,
        presenter: EnumUnitValuePresenter,
    },
    Owned(Arc<dyn FrozenDyn>),
    Leash(&'static dyn ImmortalDyn),
    SizedRef(Arc<dyn FrozenDyn>),
    SizedMut(Arc<dyn FrozenDyn>),
    OptionBox(Option<Arc<dyn FrozenDyn>>),
    OptionLeash(Option<&'static dyn FrozenDyn>),
    OptionSizedRef(Option<Arc<dyn FrozenDyn>>),
    OptionSizedRefMut(Option<Arc<dyn FrozenDyn>>),
    Intrinsic(Arc<dyn FrozenDyn>),
}

impl IsFrozenValue for FrozenValue {
    type Value = Value;

    fn thaw(&self) -> (SlushValue, ThawedValue) {
        todo!()
    }

    fn present(
        &self,
        value_presenter_cache: &mut ValuePresenterCache,
        value_presentation_synchrotron: &mut ValuePresentationSynchrotron,
    ) -> ValuePresentation {
        match self {
            FrozenValue::Uninit => todo!(),
            FrozenValue::Invalid => todo!(),
            FrozenValue::Moved => todo!(),
            FrozenValue::Unit(value) => ValuePresentation::Unit(*value),
            FrozenValue::Bool(value) => ValuePresentation::Bool(*value),
            FrozenValue::Char(value) => ValuePresentation::Char(*value),
            FrozenValue::I8(value) => ValuePresentation::I8(*value),
            FrozenValue::I16(value) => ValuePresentation::I16(*value),
            FrozenValue::I32(value) => ValuePresentation::I32(*value),
            FrozenValue::I64(value) => ValuePresentation::I64(*value),
            FrozenValue::I128(value) => ValuePresentation::I128(*value),
            FrozenValue::ISize(value) => ValuePresentation::ISize(*value),
            FrozenValue::U8(value) => ValuePresentation::U8(*value),
            FrozenValue::U16(value) => ValuePresentation::U16(*value),
            FrozenValue::U32(value) => ValuePresentation::U32(*value),
            FrozenValue::U64(value) => ValuePresentation::U64(*value),
            FrozenValue::U128(value) => ValuePresentation::U128(*value),
            FrozenValue::USize(value) => ValuePresentation::USize(*value),
            FrozenValue::R8(value) => ValuePresentation::R8(*value),
            FrozenValue::R16(value) => ValuePresentation::R16(*value),
            FrozenValue::R32(value) => ValuePresentation::R32(*value),
            FrozenValue::R64(value) => ValuePresentation::R64(*value),
            FrozenValue::R128(value) => ValuePresentation::R128(*value),
            FrozenValue::RSize(value) => ValuePresentation::RSize(*value),
            FrozenValue::F32(value) => ValuePresentation::F32((*value).into()),
            FrozenValue::F64(value) => ValuePresentation::F64((*value).into()),
            FrozenValue::StringLiteral(_) => todo!(),
            FrozenValue::EnumUsize { index, presenter } => presenter(
                *index,
                value_presenter_cache,
                value_presentation_synchrotron,
            ),
            FrozenValue::Owned(arc) => (**arc).present_dyn(),
            FrozenValue::Leash(leash) => leash.present_dyn(),
            FrozenValue::SizedRef(_) => todo!(),
            FrozenValue::SizedMut(_) => todo!(),
            FrozenValue::OptionBox(_) => todo!(),
            FrozenValue::OptionLeash(_) => todo!(),
            FrozenValue::OptionSizedRef(_) => todo!(),
            FrozenValue::OptionSizedRefMut(_) => todo!(),
            FrozenValue::Intrinsic(_) => todo!(),
        }
    }

    fn visualize(&self, visual_synchrotron: &mut VisualSynchrotron) -> Visual {
        use husky_visual_protocol::visualize::Visualize;
        match *self {
            FrozenValue::Unit(_) => Visual::Void,
            FrozenValue::Bool(_) => todo!(),
            FrozenValue::Char(_) => todo!(),
            FrozenValue::I8(value) => PrimitiveVisual::I8(value).into(),
            FrozenValue::I16(_) => todo!(),
            FrozenValue::I32(_) => todo!(),
            FrozenValue::I64(_) => todo!(),
            FrozenValue::I128(_) => todo!(),
            FrozenValue::ISize(_) => todo!(),
            FrozenValue::U8(_) => todo!(),
            FrozenValue::U16(_) => todo!(),
            FrozenValue::U32(_) => todo!(),
            FrozenValue::U64(_) => todo!(),
            FrozenValue::U128(_) => todo!(),
            FrozenValue::USize(_) => todo!(),
            FrozenValue::R8(_) => todo!(),
            FrozenValue::R16(_) => todo!(),
            FrozenValue::R32(_) => todo!(),
            FrozenValue::R64(_) => todo!(),
            FrozenValue::R128(_) => todo!(),
            FrozenValue::RSize(_) => todo!(),
            FrozenValue::F32(f) => f.visualize(visual_synchrotron),
            FrozenValue::F64(_) => todo!(),
            FrozenValue::StringLiteral(_) => todo!(),
            FrozenValue::Owned(ref value) => (**value).visualize_or_void_dyn(visual_synchrotron),
            FrozenValue::Leash(value) => value.visualize_or_void_dyn(visual_synchrotron),
            FrozenValue::OptionBox(_) => todo!(),
            FrozenValue::OptionLeash(_) => todo!(),
            FrozenValue::Uninit => todo!(),
            FrozenValue::Invalid => todo!(),
            FrozenValue::Moved => todo!(),
            FrozenValue::EnumUsize { index, presenter } => todo!(),
            FrozenValue::SizedRef(_) => todo!(),
            FrozenValue::SizedMut(_) => todo!(),
            FrozenValue::OptionSizedRef(_) => todo!(),
            FrozenValue::OptionSizedRefMut(_) => todo!(),
            FrozenValue::Intrinsic(_) => todo!(),
        }
    }
}
