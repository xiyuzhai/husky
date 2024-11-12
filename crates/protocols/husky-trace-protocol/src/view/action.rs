use std::marker::PhantomData;

use husky_item_path_interface::ItemPathIdInterface;
use serde::{Deserialize, Serialize};
use smallvec::SmallVec;
use ui::app::IsParentActionBuffer;
use vec_like::SmallVecSet;

use crate::{trace_id::TraceId, IsTraceProtocol};

#[derive(Debug, Serialize, Deserialize)]
pub enum TraceViewAction<TraceProtocol: IsTraceProtocol> {
    ToggleExpansion {
        trace_id: TraceId,
    },
    ToggleAssocTrace {
        trace_id: TraceId,
        assoc_trace_id: TraceId,
    },
    FollowTrace {
        followed: TraceId,
    },
    ToggleAccompany {
        trace_id: TraceId,
    },
    SetCaryatid {
        caryatid: TraceProtocol::Caryatid,
    },
    AddExtraVarDepsToCaryatid {
        var_deps: SmallVecSet<ItemPathIdInterface, 2>,
    },
}

pub struct TraceViewActionBuffer<TraceProtocol: IsTraceProtocol> {
    actions: SmallVec<[TraceViewAction<TraceProtocol>; 2]>,
}

impl<TraceProtocol: IsTraceProtocol> Default for TraceViewActionBuffer<TraceProtocol> {
    fn default() -> Self {
        Self {
            actions: Default::default(),
        }
    }
}

impl<TraceProtocol: IsTraceProtocol> TraceViewActionBuffer<TraceProtocol> {
    pub fn push(&mut self, action: TraceViewAction<TraceProtocol>) {
        self.actions.push(action)
    }

    pub fn take_actions<ParentActionBuffer: IsParentActionBuffer>(
        &mut self,
        parent_action_buffer: &mut ParentActionBuffer,
    ) -> SmallVec<[TraceViewAction<TraceProtocol>; 2]> {
        std::mem::take(&mut self.actions)
    }
}
