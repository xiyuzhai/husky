use husky_linket_impl::{static_var::StaticVarResult, var_id::IsVarId};
use husky_value::{
    ki_control_flow::ValuePresentationKiControlFlow,
    vm_control_flow::ValuePresentationVmControlFlow,
};

use crate::*;

pub type JsonValue = serde_json::Value;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TraceStalk<VarId: IsVarId> {
    value_presentation_control_flow_result:
        StaticVarResult<VarId, Option<ValuePresentationKiControlFlow>>,
}

impl<VarId: IsVarId> TraceStalk<VarId> {
    pub fn new(
        value_presentation_control_flow_result: StaticVarResult<
            VarId,
            Option<ValuePresentationKiControlFlow>,
        >,
    ) -> Self {
        Self {
            value_presentation_control_flow_result,
        }
    }
}

impl<VarId: IsVarId> TraceStalk<VarId> {
    pub fn value_presentation_control_flow_result(
        &self,
    ) -> &StaticVarResult<VarId, Option<ValuePresentationKiControlFlow>> {
        &self.value_presentation_control_flow_result
    }
}
