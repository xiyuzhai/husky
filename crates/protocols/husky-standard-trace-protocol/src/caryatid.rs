#[cfg(feature = "egui")]
mod egui;

use super::*;
use husky_item_path_interface::ItemPathIdInterface;
use husky_linket_impl::pedestal::IsPedestal;
use husky_trace_protocol::{
    anchor::Anchor,
    caryatid::{IsCaryatid, IsCaryatidUiBuffer},
    windlass::Windlass,
};
use rustc_hash::FxHashMap;
use vec_like::ordered_small_vec_map::OrderedSmallVecPairMap;

#[derive(Default, Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct StandardCaryatid {
    windlasses: OrderedSmallVecPairMap<ItemPathIdInterface, Windlass<StandardVarId>, 2>,
}

impl std::ops::Index<ItemPathIdInterface> for StandardCaryatid {
    type Output = Windlass<StandardVarId>;

    fn index(&self, item_path_id_interface: ItemPathIdInterface) -> &Self::Output {
        &self.windlasses[item_path_id_interface].1
    }
}

impl IsCaryatid for StandardCaryatid {
    type Pedestal = StandardPedestal;

    fn pedestal(&self, var_deps: &[ItemPathIdInterface]) -> Option<Self::Pedestal> {
        var_deps
            .iter()
            .copied()
            .map(|dep| {
                self.windlasses
                    .get_value(dep)
                    .copied()
                    .map(|windlass| match windlass {
                        Windlass::Specific(var_id) | Windlass::Generic { moored: var_id, .. } => {
                            Some((dep, var_id))
                        }
                        _ => None,
                    })
                    .flatten()
            })
            .collect()
    }

    fn has_var_deps(&self, var_deps: &[ItemPathIdInterface]) -> bool {
        var_deps.iter().copied().all(|dep| self.windlasses.has(dep))
    }

    type UiBuffer = StandardCaryatidUiBuffer;

    // fn with_extra_var_deps(&self, var_deps: &[ItemPathIdInterface]) -> Self {
    //     let mut slf = self.clone();
    //     slf.windlasses.extend(
    //         var_deps.iter().map(|&var_dep| {
    //             (
    //                 var_dep,
    //                 Windlass::Generic {
    //                     followed: None,
    //                     page_start: todo!(),
    //                     page_limit: Some(100),
    //                 },
    //             )
    //         }), // ad hoc
    //     );
    //     slf
    // }

    fn windlasses(
        &self,
    ) -> &[(
        ItemPathIdInterface,
        Windlass<<Self::Pedestal as IsPedestal>::VarId>,
    )] {
        &self.windlasses
    }

    fn add_new(
        &mut self,
        item_path_id_interface: ItemPathIdInterface,
        windlass: Windlass<<Self::Pedestal as IsPedestal>::VarId>,
    ) {
        self.windlasses
            .insert_new((item_path_id_interface, windlass))
            .unwrap()
    }

    fn has_var_dep(&self, var_dep: ItemPathIdInterface) -> bool {
        self.windlasses.has(var_dep)
    }
}

impl StandardCaryatid {
    /// empty returns true, intentionally
    pub fn is_specific(&self) -> bool {
        self.windlasses
            .iter()
            .copied()
            .all(|(_, windlass)| windlass.is_specific())
    }
}

#[test]
fn standard_caryatid_is_specific_works() {
    let mut caryatid = StandardCaryatid::default();
    assert!(caryatid.is_specific());
}

#[derive(Debug, Default)]
pub struct StandardCaryatidUiBuffer {
    var_id_edits: FxHashMap<ItemPathIdInterface, String>,
}

impl IsCaryatidUiBuffer for StandardCaryatidUiBuffer {
    type Caryatid = StandardCaryatid;

    fn show_var_id_edit<TraceProtocol>(
        &mut self,
        item_path_id_interface: ItemPathIdInterface,
        var_id: Option<<<Self::Caryatid as IsCaryatid>::Pedestal as IsPedestal>::VarId>,
        trace_synchrotron: &husky_trace_protocol::synchrotron::TraceSynchrotron<TraceProtocol>,
    ) where
        TraceProtocol: IsTraceProtocol<
            Pedestal = <Self::Caryatid as IsCaryatid>::Pedestal,
            Caryatid = Self::Caryatid,
        >,
    {
        assert!(!self.var_id_edits.contains_key(&item_path_id_interface));
        self.var_id_edits.insert(
            item_path_id_interface,
            var_id
                .map(|var_id| {
                    trace_synchrotron
                        .var_id_presentation(item_path_id_interface, var_id)
                        .data()
                })
                .unwrap_or_default()
                .to_string(),
        );
    }

    fn var_id_edit(&mut self, item_path_id_interface: ItemPathIdInterface) -> Option<&mut String> {
        self.var_id_edits.get_mut(&item_path_id_interface)
    }
}
