#[cfg(feature = "test_helpers")]
pub mod test_helpers;

use self::accompany::AccompanyingTraceIdsExceptFollowed;
use crate::{
    message::{TraceRequest, TraceResponse},
    synchrotron::action::{
        TraceSynchrotronActionNewTrace, TraceSynchrotronActionSetSubtraces,
        TraceSynchrotronActionToggleExpansion,
    },
    view::{action::TraceViewAction, TraceViewData},
    *,
};
use figure::TraceFigureKey;
use husky_item_path_interface::ItemPathIdInterface;
use husky_ki_repr_interface::KiReprInterface;
use husky_linket_impl::{
    pedestal::{IsPedestal, IsPedestalFull},
    static_var::StaticVarResult,
};
use husky_value_protocol::presentation::{
    synchrotron::ValuePresentationSynchrotron, ValuePresenterCache,
};
use husky_visual_protocol::{plot::PlotClass, synchrotron::VisualSynchrotron, visual::Visual};
use husky_websocket_utils::easy_server::IsEasyWebsocketServer;
use item_path::ItemPathPresentation;
use rustc_hash::FxHashMap;
use shifted_unsigned_int::ShiftedU32;
use smallvec::*;
use std::net::ToSocketAddrs;
use var_id::VarIdPresentation;
use vec_like::{ordered_small_vec_map::OrderedSmallVecPairMap, OrderedSmallVecSet};

pub struct TraceServer<Tracetime: IsTracetime> {
    trace_synchrotron: Option<TraceSynchrotron<Tracetime::TraceProtocol>>,
    value_presenter_cache: ValuePresenterCache,
    visual_cache: TraceVisualCache<<Tracetime::TraceProtocol as IsTraceProtocol>::Pedestal>,
    tracetime: Tracetime,
}

/// this struct storages mapping from trace id and pedestal to visual,
///
/// useful for calculating figure,
///
/// but the client doesn't need to know about this
pub struct TraceVisualCache<Pedestal: IsPedestalFull> {
    trace_plot_classes: FxHashMap<TraceId, PlotClass>,
    trace_plot_maps: FxHashMap<OrderedSmallVecSet<TraceId, 4>, TracePlotInfos>,
    visuals: FxHashMap<(TraceId, Pedestal), Visual>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct TracePlotInfos {
    /// the class for each plot
    data: SmallVec<[(OrderedSmallVecSet<TraceId, 2>, PlotClass); 4]>,
}

impl std::ops::Deref for TracePlotInfos {
    type Target = SmallVec<[(OrderedSmallVecSet<TraceId, 2>, PlotClass); 4]>;

    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

impl TracePlotInfos {
    fn new(
        traces: OrderedSmallVecSet<TraceId, 4>,
        trace_plot_classes: &FxHashMap<TraceId, PlotClass>,
    ) -> Self {
        let mut data: SmallVec<[(OrderedSmallVecSet<TraceId, 2>, PlotClass); 4]> = smallvec![];
        for trace_id in traces {
            let plot_class = *trace_plot_classes
                .get(&trace_id)
                .unwrap_or(&PlotClass::Void);
            match plot_class {
                PlotClass::Void => (),
                PlotClass::Graphics2D | PlotClass::Graphics3D => {
                    let mut flag = false;
                    for &mut (ref mut traces, plot_class0) in &mut data {
                        if plot_class0 == plot_class {
                            traces.insert(trace_id);
                            flag = true;
                            break;
                        }
                    }
                    if !flag {
                        data.push((OrderedSmallVecSet::new_one_elem_set(trace_id), plot_class))
                    }
                }
                PlotClass::Any => {
                    data.push((OrderedSmallVecSet::new_one_elem_set(trace_id), plot_class))
                }
            }
        }
        Self { data }
    }
}

impl<Pedestal: IsPedestalFull> TraceVisualCache<Pedestal> {
    pub fn visual(
        &mut self,
        trace_id: TraceId,
        pedestal: Pedestal,
        f: impl FnOnce() -> (Visual, PlotClass),
    ) -> Visual {
        *self.visuals.entry((trace_id, pedestal)).or_insert_with(|| {
            let (visual, plot_class) = f();
            match self.trace_plot_classes.entry(trace_id) {
                std::collections::hash_map::Entry::Occupied(mut entry) => {
                    entry.get_mut().merge(plot_class);
                }
                std::collections::hash_map::Entry::Vacant(mut entry) => {
                    entry.insert(plot_class);
                }
            }
            visual
        })
    }

    // todo: caching this??
    pub fn calc_plots<'a>(
        &'a mut self,
        traces: OrderedSmallVecSet<TraceId, 4>,
    ) -> &'a TracePlotInfos {
        self.trace_plot_maps
            .entry(traces.clone())
            .or_insert_with(|| TracePlotInfos::new(traces, &self.trace_plot_classes))
    }
}

impl<Pedestal: IsPedestalFull> Default for TraceVisualCache<Pedestal> {
    fn default() -> Self {
        Self {
            trace_plot_classes: Default::default(),
            trace_plot_maps: Default::default(),
            visuals: Default::default(),
        }
    }
}

impl<Tracetime: IsTracetime> Default for TraceServer<Tracetime>
where
    Tracetime: Default,
{
    fn default() -> Self {
        Self {
            trace_synchrotron: Default::default(),
            value_presenter_cache: Default::default(),
            tracetime: Default::default(),
            visual_cache: Default::default(),
        }
    }
}

impl<Tracetime: IsTracetime> TraceServer<Tracetime> {
    fn new(tracetime: Tracetime) -> Self {
        let mut slf = Self {
            trace_synchrotron: Default::default(),
            tracetime,
            value_presenter_cache: Default::default(),
            visual_cache: Default::default(),
        };
        slf.init();
        slf
    }

    fn init(&mut self) {
        assert!(self.trace_synchrotron.is_none());
        let trace_bundles = self.tracetime.trace_bundles();
        self.trace_synchrotron = Some(TraceSynchrotron::new(trace_bundles, |trace| {
            (
                self.tracetime.trace_var_deps(trace),
                self.tracetime.trace_history_var_deps(trace),
                self.tracetime.trace_view_data(trace).clone(),
            )
        }));
        self.cache_peripheries()
    }

    #[track_caller]
    fn trace_synchrotron(&self) -> &TraceSynchrotron<Tracetime::TraceProtocol> {
        self.trace_synchrotron.as_ref().unwrap()
    }

    #[track_caller]
    fn trace_synchrotron_mut(&mut self) -> &mut TraceSynchrotron<Tracetime::TraceProtocol> {
        self.trace_synchrotron.as_mut().unwrap()
    }
}

impl<Tracetime> IsEasyWebsocketServer for TraceServer<Tracetime>
where
    Tracetime: IsTracetime,
    Tracetime::TraceProtocol: Serialize + for<'a> Deserialize<'a>,
{
    type Response = TraceResponse<Tracetime::TraceProtocol>;

    type Request = TraceRequest<Tracetime::TraceProtocol>;

    type SerdeImpl = Tracetime::SerdeImpl;

    fn handle(&mut self, request: Self::Request) -> Option<Self::Response> {
        match request {
            TraceRequest::Init {
                trace_protocol_type_name,
            } => {
                if trace_protocol_type_name != std::any::type_name::<Tracetime::TraceProtocol>() {
                    // todo: make this a type
                    return Some(TraceResponse::Err(format!(
                        r#"server's trace protocol is of type `{},
but client's trace protocol is of type `{trace_protocol_type_name}`."#,
                        std::any::type_name::<Tracetime::TraceProtocol>()
                    )));
                }
                let Some(trace_synchrotron) = self.trace_synchrotron.clone() else {
                    unreachable!()
                };
                Some(TraceResponse::Init { trace_synchrotron })
            }
            TraceRequest::TakeViewAction {
                view_action,
                trace_synchrotron_status,
            } => {
                let Some(ref mut _cache) = self.trace_synchrotron else {
                    unreachable!()
                };
                assert_eq!(self.trace_synchrotron().status(), trace_synchrotron_status);
                self.take_view_action(view_action);
                let trace_synchrotron_actions_diff = self
                    .trace_synchrotron()
                    .actions_diff(trace_synchrotron_status);
                Some(TraceResponse::TakeTraceSynchrotronActionsDiff {
                    trace_synchrotron_actions_diff,
                })
            }
            TraceRequest::NotifyViewAction {
                trace_synchrotron_action,
                ..
            } => {
                self.trace_synchrotron_mut()
                    .take_action(trace_synchrotron_action);
                None
            }
        }
    }
}

impl<Tracetime: IsTracetime> TraceServer<Tracetime> {
    fn take_view_action(&mut self, view_action: TraceViewAction<Tracetime::TraceProtocol>) {
        match view_action {
            TraceViewAction::ToggleExpansion { trace_id } => {
                assert!(!self.trace_synchrotron()[trace_id].expanded());
                // todo: handle more cases like subtraces with channels
                if self.trace_synchrotron()[trace_id].subtrace_ids().is_some() {
                    return;
                }
                let subtraces = self.tracetime.subtraces(trace_id.into()).to_vec();
                let subtrace_ids = subtraces
                    .into_iter()
                    .map(|subtrace| {
                        let subtrace_id = subtrace.into();
                        self.cache_trace_if_new(subtrace_id);
                        subtrace_id
                    })
                    .collect();
                self.trace_synchrotron_mut()
                    .take_action(TraceSynchrotronActionSetSubtraces::new(
                        trace_id,
                        subtrace_ids,
                    ));
                self.trace_synchrotron_mut()
                    .take_action(TraceSynchrotronActionToggleExpansion::new(trace_id))
            }
            TraceViewAction::ToggleAssocTrace {
                trace_id,
                assoc_trace_id,
            } => {
                self.cache_trace_if_new(assoc_trace_id);
                self.trace_synchrotron_mut()
                    .take_action(TraceSynchrotronAction::ToggleAssocTrace {
                        trace_id,
                        assoc_trace_id,
                    })
            }
            TraceViewAction::FollowTrace { followed: trace_id } => self
                .trace_synchrotron_mut()
                .take_action(TraceSynchrotronAction::FollowTrace { followed: trace_id }),
            TraceViewAction::ToggleAccompany { trace_id } => self
                .trace_synchrotron_mut()
                .take_action(TraceSynchrotronAction::ToggleAccompany { trace_id }),
            TraceViewAction::SetCaryatid { caryatid } => self
                .trace_synchrotron_mut()
                .take_action(TraceSynchrotronAction::SetCaryatid { caryatid }),
            TraceViewAction::AddExtraVarDepsToCaryatid { ref var_deps } => {
                let Ok(caryatid) = self.tracetime.add_extra_var_deps_to_caryatid(
                    self.trace_synchrotron().caryatid().clone(),
                    var_deps,
                    50, // ad hoc
                ) else {
                    todo!()
                };
                self.trace_synchrotron_mut()
                    .take_action(TraceSynchrotronAction::SetCaryatid { caryatid })
            }
        }
        self.cache_peripheries()
    }

    fn cache_trace_if_new(&mut self, trace_id: TraceId) {
        if !self.trace_synchrotron().is_trace_cached(trace_id) {
            let var_deps = self.tracetime.trace_var_deps(trace_id.into());
            let history_var_deps = self.tracetime.trace_history_var_deps(trace_id.into());
            let view_data = self.tracetime.trace_view_data(trace_id.into());
            self.trace_synchrotron_mut()
                .take_action(TraceSynchrotronActionNewTrace::new(
                    trace_id,
                    var_deps,
                    history_var_deps,
                    view_data,
                ))
        }
    }

    fn cache_peripheries(&mut self) {
        self.cache_item_path_presentations();
        self.cache_stalks();
        self.cache_figure()
    }

    fn cache_item_path_presentations(&mut self) {
        self.trace_synchrotron
            .as_mut()
            .unwrap()
            .cache_item_path_presentations(|item_path_id_interface| {
                self.tracetime
                    .calc_item_path_presentations(item_path_id_interface)
            })
    }

    fn cache_stalks(&mut self) {
        use crate::caryatid::IsCaryatid;
        let trace_listing = self.trace_synchrotron().trace_listing();
        for trace_id in trace_listing {
            if let Some(pedestal) = self
                .trace_synchrotron()
                .caryatid()
                .pedestal(&self.trace_synchrotron()[trace_id].var_deps())
            {
                self.cache_stalk(trace_id, pedestal)
            }
        }
    }

    fn cache_stalk(
        &mut self,
        trace_id: TraceId,
        pedestal: <Tracetime::TraceProtocol as IsTraceProtocol>::Pedestal,
    ) {
        if !self.trace_synchrotron()[trace_id].has_stalk(&pedestal) {
            let trace_synchrotron = self.trace_synchrotron.as_mut().unwrap();
            let stalk = self.tracetime.calc_trace_stalk(
                trace_id.into(),
                &pedestal,
                &mut self.value_presenter_cache,
                trace_synchrotron.value_presentation_synchrotron_mut(),
            );
            trace_synchrotron.take_action(TraceSynchrotronAction::CacheStalk {
                pedestal: pedestal.clone(),
                trace_id,
                stalk,
            });
        }
    }

    fn cache_figure(&mut self) {
        let trace_synchrotron = self.trace_synchrotron.as_mut().unwrap();
        for figure_key in trace_synchrotron.figure_keys() {
            if !trace_synchrotron.has_figure(&figure_key) {
                let figure = self.tracetime.calc_figure(
                    &figure_key,
                    trace_synchrotron.visual_synchrotron_mut(),
                    &mut self.visual_cache,
                );
                trace_synchrotron.cache_var_id_presentations_from_figure(&figure, |var_id| {
                    self.tracetime.calc_var_id_presentations(var_id)
                });
                trace_synchrotron
                    .take_action(TraceSynchrotronAction::CacheFigure { figure_key, figure })
            }
        }
    }

    fn cache_var_id_presentations_from_caryatid(&mut self) {
        self.trace_synchrotron.as_mut().unwrap().caryatid();
        self.trace_synchrotron
            .as_mut()
            .unwrap()
            .cache_var_id_presentations_from_caryatid(|var_id| {
                self.tracetime.calc_var_id_presentations(var_id)
            })
    }
}

pub trait IsTracetime: Send + 'static + Sized {
    type Trace: IsTrace;
    //  Send + Eq + std::hash::Hash + Copy;

    type TraceProtocol: IsTraceProtocolFull;

    type SerdeImpl: serde_impl::IsSerdeImpl;

    /// final
    fn serve_traces(self, addr: impl std::fmt::Debug + ToSocketAddrs) {
        TraceServer::new(self).easy_serve(addr)
    }

    fn trace_bundles(&self) -> &[TraceBundle<Self::Trace>];

    fn subtraces(&self, trace: Self::Trace) -> &[Self::Trace];

    fn trace_var_deps(&self, trace: Self::Trace) -> SmallVec<[ItemPathIdInterface; 2]>;

    fn trace_history_var_deps(
        &self,
        trace: Self::Trace,
    ) -> Option<SmallVec<[ItemPathIdInterface; 2]>>;

    fn trace_view_data(&self, trace: Self::Trace) -> TraceViewData;

    fn add_extra_var_deps_to_caryatid(
        &self,
        caryatid: <Self::TraceProtocol as IsTraceProtocol>::Caryatid,
        var_deps: &[ItemPathIdInterface],
        page_limit: usize,
    ) -> StaticVarResult<
        TraceVarId<Self::TraceProtocol>,
        <Self::TraceProtocol as IsTraceProtocol>::Caryatid,
    >;

    fn calc_trace_stalk(
        &self,
        trace: Self::Trace,
        pedestal: &<Self::TraceProtocol as IsTraceProtocol>::Pedestal,
        value_presenter_cache: &mut ValuePresenterCache,
        value_presentation_synchrotron: &mut ValuePresentationSynchrotron,
    ) -> TraceStalk<<<Self::TraceProtocol as IsTraceProtocol>::Pedestal as IsPedestal>::VarId>;

    fn calc_figure(
        &self,
        figure_key: &TraceFigureKey<Self::TraceProtocol>,
        visual_synchrotron: &mut VisualSynchrotron,
        trace_visual_cache: &mut TraceVisualCache<
            <Self::TraceProtocol as IsTraceProtocol>::Pedestal,
        >,
    ) -> <Self::TraceProtocol as IsTraceProtocol>::Figure;

    fn calc_item_path_presentations(
        &self,
        item_path_id_interface: ItemPathIdInterface,
    ) -> ItemPathPresentation;
    fn calc_var_id_presentations(
        &self,
        var_id: TraceVarId<Self::TraceProtocol>,
    ) -> VarIdPresentation;
}
