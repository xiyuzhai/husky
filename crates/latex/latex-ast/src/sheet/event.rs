use super::*;
use time_capsule::event::{IsTimeCapsuleEvent, IsTimeCapsuleEventBuffer};

pub struct MathAstEvent {}

impl IsTimeCapsuleEvent for MathAstEvent {
    type Buffer = MathAstEventBuffer;

    type State = LxAstSheet;
}

#[derive(Default)]
pub struct MathAstEventBuffer {}

impl IsTimeCapsuleEventBuffer for MathAstEventBuffer {
    type Event = MathAstEvent;

    fn finish(self) -> Option<Self::Event> {
        todo!()
    }
}
