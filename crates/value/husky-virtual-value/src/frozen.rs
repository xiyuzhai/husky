use crate::*;
use husky_value::IsFrozenValue;
use husky_value_protocol::presentation::{
    synchrotron::ValuePresentationSynchrotron, ValuePresentation, ValuePresenterCache,
};
use husky_visual_protocol::synchrotron::VisualSynchrotron;
use value::Value;

impl IsFrozenValue for Value {
    type Value = Value;

    fn thaw(&self) -> ((), Value) {
        todo!()
    }

    fn present(
        &self,
        value_presenter_cache: &mut ValuePresenterCache,
        value_presentation_synchrotron: &mut ValuePresentationSynchrotron,
    ) -> ValuePresentation {
        todo!()
    }

    fn visualize(
        &self,
        visual_synchrotron: &mut VisualSynchrotron,
    ) -> husky_visual_protocol::visual::Visual {
        todo!()
    }
}
