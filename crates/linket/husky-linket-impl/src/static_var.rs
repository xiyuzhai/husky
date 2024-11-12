use crate::*;
use husky_figure_zone_protocol::{
    text::{FigureText, FigureTextKey},
    FigureZone,
};
use husky_value::IsValue;
use serde::{Deserialize, Serialize};
use var_id::IsVarId;

pub trait IsStaticVar<VarId: IsVarId>: 'static {
    fn item_path_id_interface() -> ItemPathIdInterface;
    fn page_var_ids<'a>(
        locked: &'a [ItemPathIdInterface],
        page_start: VarId,
        page_limit: Option<usize>,
    ) -> Box<dyn Iterator<Item = VarId> + 'a> {
        if locked.contains(&Self::item_path_id_interface()) {
            return Box::new([Self::get_id()].into_iter());
        }
        Box::new(unsafe { Self::page_var_ids_aux(locked) })
    }

    fn page_var_ids_aux(locked: &[ItemPathIdInterface]) -> impl Iterator<Item = VarId>;

    fn default_page_start(
        figure_zone: FigureZone,
        locked: &[ItemPathIdInterface],
    ) -> StaticVarResult<VarId, VarId>;

    fn get_id() -> VarId;

    fn try_set_var_id(
        new: VarId,
        locked: &[ItemPathIdInterface],
    ) -> StaticVarResult<VarId, impl FnOnce() + 'static> {
        let item_path_id_interface = Self::item_path_id_interface();
        if locked.contains(&item_path_id_interface) {
            let old = Self::get_id();
            if old != new {
                Err(StaticVarError::ReplaceLocked {
                    locked_path: item_path_id_interface,
                    old,
                    new,
                })?
            }
        }
        Self::try_set_var_id_aux(new, locked)
    }

    /// returns a restore if okay,
    ///
    /// otherwise, it's guaranteed that nothing changes on the binary side if err
    fn try_set_var_id_aux(
        new: VarId,
        locked: &[ItemPathIdInterface],
    ) -> StaticVarResult<VarId, impl FnOnce() + 'static>;

    fn try_set_default_var_id(
        locked: &[ItemPathIdInterface],
    ) -> StaticVarResult<VarId, (VarId, impl FnOnce() + 'static)>;

    fn with_var_id<R>(
        var_id: VarId,
        locked: &[ItemPathIdInterface],
        f: impl FnOnce() -> R,
    ) -> StaticVarResult<VarId, R> {
        let restore = unsafe { Self::try_set_var_id(var_id, locked) }?;
        let r = f();
        restore();
        Ok(r)
    }

    type Value: IsValue;

    fn get_value() -> Self::Value;

    fn zones() -> &'static [FigureZone];

    /// override if necessary
    fn text_key(var_id: VarId) -> FigureTextKey<VarId> {
        unreachable!(
            "IsStaticVar::text_key() not implemented for `{}`",
            std::any::type_name::<Self>()
        )
    }

    /// override if necessary
    fn text(key: FigureTextKey<VarId>) -> FigureText {
        unreachable!(
            "IsStaticVar::text() not implemented for `{}`",
            std::any::type_name::<Self>()
        )
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct StaticVarSvtable<VarId: IsVarId, Value: IsValue> {
    get_var_id: fn() -> VarId,
    page_var_ids: for<'db> fn(
        &'db [ItemPathIdInterface],
        VarId,
        Option<usize>,
    ) -> Box<dyn Iterator<Item = VarId> + 'db>,
    default_page_start: fn(FigureZone, &[ItemPathIdInterface]) -> StaticVarResult<VarId, VarId>,
    // todo: use guard?
    try_set_var_id: unsafe fn(
        VarId,
        locked: &[ItemPathIdInterface],
    ) -> StaticVarResult<VarId, Box<dyn FnOnce() + 'static>>,
    try_set_default_var_id:
        unsafe fn(
            locked: &[ItemPathIdInterface],
        ) -> StaticVarResult<VarId, (VarId, Box<dyn FnOnce() + 'static>)>,
    get_value: fn() -> Value,
    zones: fn() -> &'static [FigureZone], // because rust doesn't support associated static items
}

impl<VarId: IsVarId, Value: IsValue> StaticVarSvtable<VarId, Value> {
    pub const fn new<V: IsStaticVar<VarId, Value = Value>>() -> Self {
        Self {
            get_var_id: V::get_id,
            try_set_var_id: |id, locked| unsafe {
                V::try_set_var_id(id, locked)
                    .map(|restore| -> Box<dyn FnOnce()> { Box::new(restore) })
            },
            try_set_default_var_id: |locked| unsafe {
                V::try_set_default_var_id(locked).map(
                    |(default, restore)| -> (VarId, Box<dyn FnOnce()>) {
                        (default, Box::new(restore))
                    },
                )
            },
            page_var_ids: |locked, page_start, page_limit| {
                Box::new(V::page_var_ids(locked, page_start, page_limit))
            },
            default_page_start: V::default_page_start,
            get_value: V::get_value,
            zones: V::zones,
        }
    }

    pub fn get_var_id(&self) -> VarId {
        (self.get_var_id)()
    }

    pub fn page_var_ids<'db>(
        &self,
        locked: &'db [ItemPathIdInterface],
        page_start: VarId,
        page_limit: Option<usize>,
    ) -> Box<dyn Iterator<Item = VarId> + 'db> {
        (self.page_var_ids)(locked, page_start, page_limit)
    }

    pub fn default_page_start(
        &self,
        zone: FigureZone,
        locked: &[ItemPathIdInterface],
    ) -> StaticVarResult<VarId, VarId> {
        (self.default_page_start)(zone, locked)
    }

    pub unsafe fn try_set_var_id(
        &self,
        var_id: VarId,
        locked: &[ItemPathIdInterface],
    ) -> StaticVarResult<VarId, Box<dyn FnOnce() + 'static>> {
        (self.try_set_var_id)(var_id, locked)
    }

    pub unsafe fn try_set_default_var_id(
        &self,
        locked: &[ItemPathIdInterface],
    ) -> StaticVarResult<VarId, (VarId, Box<dyn FnOnce() + 'static>)> {
        (self.try_set_default_var_id)(locked)
    }

    pub fn get_value(&self) -> Value {
        (self.get_value)()
    }

    pub fn zones(&self) -> &'static [FigureZone] {
        (self.zones)()
    }
}

/// this is a mild error, sometimes intentionally triggered
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum StaticVarError<VarId> {
    ReplaceLocked {
        locked_path: ItemPathIdInterface,
        old: VarId,
        new: VarId,
    },
}

pub type StaticVarResult<VarId, T> = Result<T, StaticVarError<VarId>>;
