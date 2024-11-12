pub mod accompany;
pub(crate) mod action;
pub mod bundle;
mod cache;
mod entry;

pub use self::action::TraceSynchrotronAction;
pub use self::entry::TraceSynchrotronEntry;

use self::action::TraceSynchrotronActionsDiff;
use self::bundle::TraceIdBundle;
use crate::{
    item_path::ItemPathPresentation, synchrotron::accompany::AccompanyingTraceIdsExceptFollowed,
    var_id::VarIdPresentation, view::TraceViewData, *,
};
use figure::{FigureKey, TraceFigureKey, TraceFigureKeys};
use husky_item_path_interface::ItemPathIdInterface;
use husky_value_protocol::presentation::synchrotron::{
    ValuePresentationSynchrotron, ValuePresentationSynchrotronStatus,
};
use husky_visual_protocol::synchrotron::{action::VisualSynchrotronStatus, VisualSynchrotron};
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use std::path::{Path, PathBuf};

/// contains information about traces that are synced across server and client
#[serde_with::serde_as]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TraceSynchrotron<TraceProtocol: IsTraceProtocol> {
    caryatid: TraceProtocol::Caryatid,
    accompanyings: AccompanyingTraceIds,
    trace_id_bundles: Vec<TraceIdBundle>,
    followed_trace_id: Option<TraceId>,
    #[serde_as(as = "Vec<(_, _)>")]
    entries: FxHashMap<TraceId, TraceSynchrotronEntry<TraceProtocol>>,
    #[serde_as(as = "Vec<(_, _)>")]
    item_path_presentations: FxHashMap<ItemPathIdInterface, ItemPathPresentation>,
    #[serde_as(as = "Vec<(_, _)>")]
    var_id_presentations:
        FxHashMap<(ItemPathIdInterface, TraceVarId<TraceProtocol>), VarIdPresentation>,
    #[serde_as(as = "Vec<(_, _)>")]
    figure_cache: FxHashMap<TraceFigureKey<TraceProtocol>, TraceProtocol::Figure>,
    actions: Vec<TraceSynchrotronAction<TraceProtocol>>,
    // child synchrotrons
    value_presentation_synchrotron: ValuePresentationSynchrotron,
    visual_synchrotron: VisualSynchrotron,
}

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct TraceSynchrotronStatus {
    actions_len: usize,
    value_presentation_synchrotron_status: ValuePresentationSynchrotronStatus,
    visual_synchrotron_status: VisualSynchrotronStatus,
}

/// # methods
impl<TraceProtocol: IsTraceProtocol> TraceSynchrotron<TraceProtocol> {
    pub(crate) fn new<Trace: IsTrace>(
        trace_bundles: &[TraceBundle<Trace>],
        f: impl Fn(
            Trace,
        ) -> (
            SmallVec<[ItemPathIdInterface; 2]>,
            Option<SmallVec<[ItemPathIdInterface; 2]>>,
            TraceViewData,
        ),
    ) -> Self {
        let mut entries: FxHashMap<TraceId, TraceSynchrotronEntry<TraceProtocol>> =
            Default::default();
        let mut trace_id_bundles: Vec<TraceIdBundle> = vec![];
        for trace_bundle in trace_bundles {
            let mut root_trace_ids: Vec<TraceId> = vec![];
            for &root_trace in trace_bundle.root_traces() {
                let root_trace_id = root_trace.into();
                root_trace_ids.push(root_trace_id);
                let (var_deps, history_var_deps, view_data) = f(root_trace);
                assert!(entries
                    .insert(
                        root_trace_id,
                        TraceSynchrotronEntry::new(var_deps, history_var_deps, view_data)
                    )
                    .is_none())
            }
            trace_id_bundles.push(TraceIdBundle::new(
                trace_bundle.crate_root_module_file_abs_path().to_owned(),
                root_trace_ids,
            ))
        }
        Self {
            caryatid: Default::default(),
            trace_id_bundles,
            entries,
            actions: vec![],
            value_presentation_synchrotron: Default::default(),
            visual_synchrotron: Default::default(),
            followed_trace_id: None,
            item_path_presentations: Default::default(),
            var_id_presentations: Default::default(),
            accompanyings: Default::default(),
            figure_cache: Default::default(),
        }
    }
}

impl<TraceProtocol: IsTraceProtocol> TraceSynchrotron<TraceProtocol> {
    pub fn trace_id_bundles(&self) -> &[TraceIdBundle] {
        &self.trace_id_bundles
    }

    pub fn visual_synchrotron(&self) -> &VisualSynchrotron {
        &self.visual_synchrotron
    }

    pub fn item_path_presentation(
        &self,
        item_path_id_interface: ItemPathIdInterface,
    ) -> &ItemPathPresentation {
        &self.item_path_presentations[&item_path_id_interface]
    }

    pub fn var_id_presentation(
        &self,
        item_path_id_interface: ItemPathIdInterface,
        var_id: TraceVarId<TraceProtocol>,
    ) -> &VarIdPresentation {
        &self.var_id_presentations[&(item_path_id_interface, var_id)]
    }

    #[track_caller]
    pub fn figures(&self) -> impl Iterator<Item = &TraceProtocol::Figure> {
        self.figure_keys()
            .into_iter()
            .map(move |key| &self.figure_cache[&key])
    }

    pub fn figure_keys(&self) -> TraceFigureKeys<TraceProtocol> {
        FigureKey::collect_from_caryatid(
            self.followed(),
            self.accompanyings_except_followed(self.followed()),
            self.caryatid(),
            self,
        )
    }

    pub(crate) fn status(&self) -> TraceSynchrotronStatus {
        TraceSynchrotronStatus {
            actions_len: self.actions.len(),
            value_presentation_synchrotron_status: self.value_presentation_synchrotron.status(),
            visual_synchrotron_status: self.visual_synchrotron.status(),
        }
    }

    pub fn accompanied(&self, trace_id: TraceId) -> bool {
        self.accompanyings.contains(&trace_id)
    }

    pub(crate) fn actions_diff(
        &self,
        previous_trace_synchrotron_status: TraceSynchrotronStatus,
    ) -> TraceSynchrotronActionsDiff<TraceProtocol> {
        assert!(previous_trace_synchrotron_status.actions_len < self.actions.len());
        let actions = self.actions[previous_trace_synchrotron_status.actions_len..]
            .iter()
            .map(|action| action.clone())
            .collect();
        let value_presentation_actions_diff = self
            .value_presentation_synchrotron
            .actions_diff(previous_trace_synchrotron_status.value_presentation_synchrotron_status);
        let visual_actions_diff = self
            .visual_synchrotron
            .actions_diff(previous_trace_synchrotron_status.visual_synchrotron_status);
        TraceSynchrotronActionsDiff::new(
            actions,
            value_presentation_actions_diff,
            visual_actions_diff,
        )
    }

    pub(crate) fn is_trace_cached(&self, trace_id: TraceId) -> bool {
        self.entries.contains_key(&trace_id)
    }

    pub(crate) fn trace_listing(&self) -> Vec<TraceId> {
        let mut trace_listings: Vec<TraceId> = vec![];
        for trace_bundle in self.trace_id_bundles() {
            for &root_trace_id in trace_bundle.root_trace_ids() {
                self.trace_listing_aux(root_trace_id, &mut trace_listings)
            }
        }
        trace_listings
    }

    fn trace_listing_aux(&self, trace_id: TraceId, trace_listings: &mut Vec<TraceId>) {
        trace_listings.push(trace_id);
        let entry = &self[trace_id];
        for &assoc_trace_id in entry.assoc_trace_ids() {
            self.trace_listing_aux(assoc_trace_id, trace_listings)
        }
        if entry.expanded() {
            for &subtrace_id in entry.subtrace_ids().unwrap() {
                self.trace_listing_aux(subtrace_id, trace_listings)
            }
        }
    }

    pub fn caryatid(&self) -> &TraceProtocol::Caryatid {
        &self.caryatid
    }

    pub(crate) fn value_presentation_synchrotron_mut(
        &mut self,
    ) -> &mut ValuePresentationSynchrotron {
        &mut self.value_presentation_synchrotron
    }

    pub fn followed(&self) -> Option<TraceId> {
        self.followed_trace_id
    }

    pub fn accompanying_trace_ids(&self) -> &AccompanyingTraceIds {
        &self.accompanyings
    }

    pub fn accompanyings_except_followed(
        &self,
        followed: Option<TraceId>,
    ) -> AccompanyingTraceIdsExceptFollowed {
        AccompanyingTraceIdsExceptFollowed::new(followed, self.accompanyings.clone())
    }

    pub fn has_figure(&self, figure_key: &TraceFigureKey<TraceProtocol>) -> bool {
        self.figure_cache.contains_key(figure_key)
    }

    pub fn has_all_figures<I>(&self, figure_keys: I) -> bool
    where
        I: IntoIterator<Item = TraceFigureKey<TraceProtocol>>,
    {
        figure_keys.into_iter().all(|key| self.has_figure(&key))
    }

    pub(crate) fn cache_figure(
        &mut self,
        key: TraceFigureKey<TraceProtocol>,
        figure: TraceProtocol::Figure,
    ) {
        assert!(self.figure_cache.insert(key, figure).is_none())
    }

    pub(crate) fn visual_synchrotron_mut(&mut self) -> &mut VisualSynchrotron {
        &mut self.visual_synchrotron
    }
}

impl<TraceProtocol: IsTraceProtocol> std::ops::Index<TraceId> for TraceSynchrotron<TraceProtocol> {
    type Output = TraceSynchrotronEntry<TraceProtocol>;

    fn index(&self, id: TraceId) -> &Self::Output {
        &self.entries[&id]
    }
}

impl<TraceProtocol: IsTraceProtocol> std::ops::IndexMut<TraceId>
    for TraceSynchrotron<TraceProtocol>
{
    #[track_caller]
    fn index_mut(&mut self, id: TraceId) -> &mut Self::Output {
        self.entries.get_mut(&id).unwrap()
    }
}
