pub mod virtual_pedestal;

use crate::ItemPathIdInterface;
use crate::{
    static_var::IsStaticVar,
    var_id::{IsVarId, IsVarIdFull},
};
use serde::{Deserialize, Serialize};
use vec_like::ordered_small_vec_map::OrderedSmallVecPairMap;

/// pedestal is a map from static var path to id
///
/// the map must be ordered according to static var path
pub trait IsPedestal:
    std::fmt::Debug
    + Default
    + PartialEq
    + Eq
    + Clone
    + Send
    + Sync
    + std::hash::Hash
    + 'static
    + FromIterator<(ItemPathIdInterface, Self::VarId)>
{
    type VarId: IsVarIdFull;

    fn exclude<V: IsStaticVar<Self::VarId>>(self) -> Self;

    fn var_ids<'a>(&'a self) -> impl Iterator<Item = (ItemPathIdInterface, Self::VarId)> + 'a;

    fn insert(&mut self, item_path_id_interface: ItemPathIdInterface, var_id: Self::VarId);

    /// a closed point in algebraic geometry is a minimal prime point locally
    fn is_closed(&self, var_deps: &[ItemPathIdInterface]) -> bool;
}

pub trait IsPedestalFull: IsPedestal + Serialize + for<'a> Deserialize<'a> {}

impl<T> IsPedestalFull for T where T: IsPedestal + Serialize + for<'a> Deserialize<'a> {}

/// This is for figure caching.
///
/// It's the combined pedestal of all relevant traces to be visualized.
///
/// we don't make it a trait because it's not likely to affect efficiency,
///
/// as it's used only in the debugger end.
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub struct JointPedestal<VarId: IsVarId> {
    data: OrderedSmallVecPairMap<ItemPathIdInterface, VarId, 4>,
}

impl<VarId: IsVarId> std::ops::Deref for JointPedestal<VarId> {
    type Target = OrderedSmallVecPairMap<ItemPathIdInterface, VarId, 4>;

    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

impl<VarId: IsVarId> JointPedestal<VarId> {
    pub fn new(data: OrderedSmallVecPairMap<ItemPathIdInterface, VarId, 4>) -> Self {
        Self { data }
    }
}

impl<VarId: IsVarId> JointPedestal<VarId> {
    /// # Panics
    ///
    /// Panics if the `var_deps` is not fully covered
    ///
    pub fn pedestal<Pedestal>(&self, var_deps: &[ItemPathIdInterface]) -> Pedestal
    where
        Pedestal: IsPedestal<VarId = VarId>,
    {
        var_deps.iter().map(|&dep| self.data[dep]).collect()
    }
}
