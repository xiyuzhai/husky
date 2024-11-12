pub mod dataset;
pub mod input_id;
pub mod task;

use self::input_id::*;
use dataset::MNIST_DATASET;
use husky_core::*;
use husky_standard_linket_impl::ugly::*;
use ml_task::label::IsLabel;

#[husky_standard_value::value_conversion]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MnistLabel {
    Zero,
    One,
    Two,
    Three,
    Four,
    Five,
    Six,
    Seven,
    Eight,
    Nine,
}

impl IsLabel for MnistLabel {
    fn label() -> Self {
        MNIST_DATASET.label(input_id())
    }
}

impl From<u8> for MnistLabel {
    fn from(value: u8) -> Self {
        unsafe { std::mem::transmute(value) }
    }
}

#[husky_standard_value::value_conversion]
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct BinaryImage28([u32; 30]);

impl BinaryImage28 {
    pub fn new_zeros() -> Self {
        Self::default()
    }

    pub fn pixel(&self, i: usize, j: usize) -> bool {
        let row = self.0[i + 1];
        (row & (1 << (29 - j))) != 0
    }
}

impl husky_core::visual::Visualize for BinaryImage28 {
    fn visualize(&self, sct: &mut __VisualSynchrotron) -> __Visual {
        __Visual::new_binary_image(
            4,
            28,
            28,
            self.0[2..]
                .iter()
                .map(|u| {
                    unsafe { std::mem::transmute::<_, [u8; 4]>(u << 2) }
                        .into_iter()
                        .rev()
                })
                .flatten()
                .collect(),
            sct,
        )
    }
}

impl std::ops::Index<usize> for BinaryImage28 {
    type Output = u32;

    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl std::ops::IndexMut<usize> for BinaryImage28 {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.0[index]
    }
}

#[husky_standard_value::value_conversion]
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct BinaryGrid28([u32; 31]);

impl BinaryGrid28 {
    pub fn new_zeros() -> Self {
        Self::default()
    }
}

impl std::ops::Index<usize> for BinaryGrid28 {
    type Output = u32;

    fn index(&self, index: usize) -> &Self::Output {
        &self.0[index]
    }
}

impl std::ops::IndexMut<usize> for BinaryGrid28 {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.0[index]
    }
}

impl BinaryGrid28 {}

#[allow(non_upper_case_globals)]
pub static mut __INPUT__ITEM_PATH_ID_INTERFACE: Option<__ItemPathIdInterface> = None;

#[allow(non_snake_case)]
pub fn INPUT() -> Leash<BinaryImage28> {
    MNIST_DATASET.input_leashed(input_id())
}

pub struct INPUT {}

impl __IsStaticVar<__VarId> for INPUT {
    fn item_path_id_interface() -> __ItemPathIdInterface {
        unsafe { __INPUT__ITEM_PATH_ID_INTERFACE.expect("__INPUT__ITEM_PATH_ID_INTERFACE") }
    }

    fn get_id() -> __VarId {
        input_id().index().into()
    }

    fn try_set_var_id_aux(
        id: __VarId,
        locked: &[__ItemPathIdInterface],
    ) -> __StaticVarResult<impl FnOnce() + 'static> {
        let old = replace_input_id(id.into());
        Ok(move || {
            set_input_id(old);
        })
    }

    fn page_var_ids_aux(locked: &[__ItemPathIdInterface]) -> impl Iterator<Item = __VarId> {
        assert!(!locked.contains(unsafe { __INPUT__ITEM_PATH_ID_INTERFACE }.as_ref().unwrap()));
        input_ids().map(Into::into)
    }

    type Value = __Value;

    fn get_value() -> Self::Value {
        INPUT().into_value()
    }

    fn default_page_start(
        figure_zone: __FigureZone,
        locked: &[__ItemPathIdInterface],
    ) -> __StaticVarResult<__VarId> {
        Ok(0u32.into())
    }

    fn try_set_default_var_id(
        locked: &[__ItemPathIdInterface],
    ) -> __StaticVarResult<(__VarId, impl FnOnce() + 'static)> {
        let default = 0usize.into();
        Ok((default, Self::try_set_var_id(default, locked)?))
    }

    fn zones() -> &'static [__FigureZone] {
        &[__FigureZone::Gallery]
    }
}

#[allow(non_upper_case_globals)]
pub static mut __TASK__ITEM_PATH_ID_INTERFACE: Option<__ItemPathIdInterface> = None;

// ad hoc
#[allow(non_snake_case)]
pub fn TASK() {}

pub struct TASK {}

impl __IsStaticVar<__VarId> for TASK {
    fn item_path_id_interface() -> __ItemPathIdInterface {
        todo!()
    }

    fn page_var_ids_aux(locked: &[__ItemPathIdInterface]) -> impl Iterator<Item = __VarId> {
        // ad hoc
        [].into_iter()
    }

    fn get_id() -> __VarId {
        todo!()
    }

    fn try_set_var_id_aux(
        id: __VarId,
        locked: &[__ItemPathIdInterface],
    ) -> __StaticVarResult<Box<dyn FnOnce()>> {
        todo!()
    }

    type Value = __Value;

    fn get_value() -> Self::Value {
        todo!()
    }

    fn default_page_start(
        figure_zone: __FigureZone,
        locked: &[__ItemPathIdInterface],
    ) -> husky_linket_impl::static_var::StaticVarResult<__VarId, __VarId> {
        todo!()
    }

    fn try_set_default_var_id(
        locked: &[__ItemPathIdInterface],
    ) -> __StaticVarResult<(__VarId, impl FnOnce() + 'static)> {
        todo!();
        Ok((todo!(), || todo!()))
    }

    fn zones() -> &'static [__FigureZone] {
        todo!()
    }
}
