//! ad hoc
use husky_standard_linket_impl::ugly::*;

#[allow(non_upper_case_globals)]
pub static mut __TASK__ITEM_PATH_ID_INTERFACE: Option<__ItemPathIdInterface> = None;

pub struct TASK;

impl __IsStaticVar<__VarId> for TASK {
    fn item_path_id_interface() -> __ItemPathIdInterface {
        todo!()
    }

    fn page_var_ids_aux(locked: &[__ItemPathIdInterface]) -> impl Iterator<Item = __VarId> {
        [].into_iter()
    }

    fn get_id() -> __VarId {
        todo!()
    }

    fn try_set_var_id_aux(
        id: __VarId,
        locked: &[__ItemPathIdInterface],
    ) -> __StaticVarResult<impl FnOnce() + 'static> {
        todo!();
        Ok(|| todo!())
    }

    type Value = __Value;

    fn get_value() -> Self::Value {
        todo!()
    }

    fn default_page_start(
        figure_zone: __FigureZone,
        locked: &[__ItemPathIdInterface],
    ) -> __StaticVarResult<__VarId> {
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
