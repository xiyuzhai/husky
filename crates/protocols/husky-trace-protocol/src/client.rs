pub mod error;
#[cfg(feature = "mock")]
pub mod mock;
#[cfg(feature = "test_helpers")]
pub mod test_helpers;

use crate::caryatid::IsCaryatid;
use crate::{
    message::*, synchrotron::action::TraceSynchrotronActionToggleExpansion,
    view::action::TraceViewAction, *,
};
use figure::FigureKey;
use husky_websocket_utils::imgui_client::{
    ImmediateWebsocketClientConnection, WebsocketClientConnectionError,
};
use notify_change::NotifyChange;
use std::sync::Arc;

use self::{accompany::AccompanyingTraceIdsExceptFollowed, caryatid::TraceCaryatidUiBuffer};

pub struct TraceClient<TraceProtocol: IsTraceProtocol, Notifier>
where
    Notifier: NotifyChange,
{
    trace_synchrotron: Option<TraceSynchrotron<TraceProtocol>>,
    connection: ImmediateWebsocketClientConnection<
        TraceRequest<TraceProtocol>,
        TraceResponse<TraceProtocol>,
        Notifier,
    >,
}

impl<TraceProtocol, Notifier> TraceClient<TraceProtocol, Notifier>
where
    TraceProtocol: IsTraceProtocolFull,
    Notifier: NotifyChange,
{
    pub fn new(
        tokio_runtime: Arc<tokio::runtime::Runtime>,
        server_address: impl Into<String>,
        notifier: Notifier,
    ) -> Self {
        Self {
            trace_synchrotron: None,
            connection: ImmediateWebsocketClientConnection::new(
                tokio_runtime,
                server_address.into(),
                notifier,
            ),
        }
    }

    pub fn update(&mut self) {
        let Some(response) = self.connection.try_recv() else {
            return;
        };
        self.process_response(response);
    }

    fn process_response(&mut self, response: TraceResponse<TraceProtocol>) {
        match response {
            TraceResponse::Init { trace_synchrotron } => {
                debug_assert!(self.trace_synchrotron.is_none());
                self.trace_synchrotron = Some(trace_synchrotron)
            }
            TraceResponse::TakeTraceSynchrotronActionsDiff {
                trace_synchrotron_actions_diff,
            } => {
                use crate::caryatid::IsCaryatidUiBuffer;

                let Some(ref mut trace_synchrotron) = self.trace_synchrotron else {
                    unreachable!()
                };
                trace_synchrotron.take_actions_diff(trace_synchrotron_actions_diff);
            }
            TraceResponse::Err(e) => panic!("{e}"),
        }
    }

    fn try_send_request(
        &mut self,
        request: TraceRequest<TraceProtocol>,
    ) -> Result<(), WebsocketClientConnectionError> {
        self.connection.try_send_request(request)
    }

    pub fn connection_error(&self) -> Option<&WebsocketClientConnectionError> {
        self.connection.error()
    }

    pub fn opt_trace_synchrotron(&self) -> Option<&TraceSynchrotron<TraceProtocol>> {
        self.trace_synchrotron.as_ref()
    }

    #[track_caller]
    fn trace_synchrotron(&self) -> &TraceSynchrotron<TraceProtocol> {
        self.trace_synchrotron.as_ref().unwrap()
    }

    #[track_caller]
    fn cache_mut(&mut self) -> &mut TraceSynchrotron<TraceProtocol> {
        self.trace_synchrotron.as_mut().unwrap()
    }

    pub fn take_view_action(
        &mut self,
        view_action: TraceViewAction<TraceProtocol>,
    ) -> Result<(), WebsocketClientConnectionError> {
        let Some(synchrotron_action) = self.try_resolve_view_action(&view_action) else {
            let trace_synchrotron_status = self.trace_synchrotron().status();
            return self.try_send_request(TraceRequest::TakeViewAction {
                view_action,
                trace_synchrotron_status,
            });
        };
        self.cache_mut().take_action(synchrotron_action.clone());
        match self.try_send_request(TraceRequest::NotifyViewAction {
            view_action,
            trace_synchrotron_action: synchrotron_action,
        }) {
            Ok(_) => (),
            Err(e) => match e {
                WebsocketClientConnectionError::SendRequestWhileCreation => todo!(),
                WebsocketClientConnectionError::SendRequestWhileDeserializingRequest => todo!(),
                WebsocketClientConnectionError::SendRequestWhileAwaitingResponse => todo!(),
                WebsocketClientConnectionError::SendRequestWhileSerializingResponse => todo!(),
                WebsocketClientConnectionError::SendRequestWhileResponseNotProcessed => {
                    let response = self.connection.try_recv();
                    todo!("SendRequestWhileResponseNotProcessed, response = {response:?}")
                }
            },
        }
        return Ok(());
    }

    /// returns Some if the action can be resolved in the client without relying on server
    fn try_resolve_view_action(
        &self,
        view_action: &TraceViewAction<TraceProtocol>,
    ) -> Option<TraceSynchrotronAction<TraceProtocol>> {
        match *view_action {
            TraceViewAction::ToggleExpansion { trace_id } => {
                let trace_cache_entry = &self.trace_synchrotron()[trace_id];
                if !trace_cache_entry.expanded() {
                    trace_cache_entry.subtrace_ids()?;
                }
                Some(TraceSynchrotronActionToggleExpansion::new(trace_id).into())
            }
            TraceViewAction::ToggleAssocTrace {
                trace_id,
                assoc_trace_id,
            } => {
                if !self.trace_synchrotron().is_trace_cached(assoc_trace_id) {
                    return None;
                }
                Some(TraceSynchrotronAction::ToggleAssocTrace {
                    trace_id,
                    assoc_trace_id,
                })
            }
            TraceViewAction::FollowTrace { followed } => {
                let trace_synchrotron = self.trace_synchrotron();
                let accompanyings_except_followed = trace_synchrotron
                    .accompanyings_except_followed(Some(followed))
                    .clone();
                let caryatid = trace_synchrotron.caryatid();
                if !trace_synchrotron.has_all_figures(FigureKey::collect_from_caryatid(
                    Some(followed),
                    accompanyings_except_followed,
                    caryatid,
                    trace_synchrotron,
                )) {
                    return None;
                }
                Some(TraceSynchrotronAction::FollowTrace { followed })
            }
            TraceViewAction::ToggleAccompany { trace_id } => {
                {
                    // see if toggling accompany will affect figure
                    let trace_synchrotron = self.trace_synchrotron();
                    let caryatid = trace_synchrotron.caryatid();
                    let mut accompanying_trace_ids =
                        trace_synchrotron.accompanying_trace_ids().clone();
                    accompanying_trace_ids.toggle(trace_id);
                    let followed = trace_synchrotron.followed();
                    if !trace_synchrotron.has_all_figures(FigureKey::collect_from_caryatid(
                        followed,
                        AccompanyingTraceIdsExceptFollowed::new(followed, accompanying_trace_ids),
                        caryatid,
                        trace_synchrotron,
                    )) {
                        return None;
                    }
                }
                Some(TraceSynchrotronAction::ToggleAccompany { trace_id })
            }
            TraceViewAction::SetCaryatid { ref caryatid } => {
                let trace_synchrotron = self.trace_synchrotron();
                {
                    use crate::caryatid::IsCaryatid;
                    // see if setting caryatid will affect stalk
                    for trace_id in trace_synchrotron.trace_listing() {
                        let entry = &trace_synchrotron[trace_id];
                        if let Some(pedestal) = caryatid.pedestal(entry.var_deps()) {
                            if !entry.has_stalk(&pedestal) {
                                return None;
                            }
                        }
                    }
                }
                {
                    // see if setting caryatid will affect figure
                    let trace_synchrotron = self.trace_synchrotron();
                    let followed = trace_synchrotron.followed();
                    let accompanyings_except_followed =
                        trace_synchrotron.accompanyings_except_followed(followed);
                    if !trace_synchrotron.has_all_figures(FigureKey::collect_from_caryatid(
                        followed,
                        accompanyings_except_followed,
                        caryatid,
                        trace_synchrotron,
                    )) {
                        return None;
                    }
                }
                Some(TraceSynchrotronAction::SetCaryatid {
                    caryatid: caryatid.clone(),
                })
            }
            TraceViewAction::AddExtraVarDepsToCaryatid { ref var_deps } => None,
        }
    }
}
