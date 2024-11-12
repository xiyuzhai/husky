use super::*;
use husky_item_path_interface::ItemPathIdInterface;
use husky_linket_impl::pedestal::{IsPedestal, JointPedestal};
use husky_linket_impl::static_var::IsStaticVar;
use var::StandardVarId;
use vec_like::ordered_small_vec_map::OrderedSmallVecPairMap;

#[derive(Debug, Default, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct StandardPedestal {
    var_ids: OrderedSmallVecPairMap<ItemPathIdInterface, StandardVarId, 2>,
}

impl FromIterator<(ItemPathIdInterface, StandardVarId)> for StandardPedestal {
    fn from_iter<T: IntoIterator<Item = (ItemPathIdInterface, StandardVarId)>>(iter: T) -> Self {
        Self {
            var_ids: iter.into_iter().collect(),
        }
    }
}

impl IsPedestal for StandardPedestal {
    type VarId = StandardVarId;

    fn exclude<V: IsStaticVar<StandardVarId>>(mut self) -> Self {
        let _ = self.var_ids.remove(V::item_path_id_interface());
        self
    }

    fn is_closed(&self, var_deps: &[ItemPathIdInterface]) -> bool {
        var_deps.iter().copied().all(|dep| self.var_ids.has(dep))
    }

    fn var_ids<'a>(&'a self) -> impl Iterator<Item = (ItemPathIdInterface, Self::VarId)> + 'a {
        self.var_ids.iter().copied()
    }

    fn insert(&mut self, item_path_id_interface: ItemPathIdInterface, var_id: Self::VarId) {
        self.var_ids.insert((item_path_id_interface, var_id));
    }
}

impl StandardPedestal {}

#[macro_export]
macro_rules! pedestal {
    ($($static_var: path),*) => {{
        [$((<$static_var>::item_path_id_interface(), <$static_var>::get_id())),*].into_iter().collect()
    }};
}

pub type StandardJointPedestal = JointPedestal<StandardVarId>;
