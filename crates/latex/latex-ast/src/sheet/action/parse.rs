//! after text editing, parse the text into a proper ast
use super::*;

pub(in crate::sheet) struct MathAstParseAction {
    ast_idx: LxAstIdx,
}

impl IsTimeCapsuleAction for MathAstParseAction {
    type Event = MathAstEvent;

    type Outcome = ();

    fn add_to_event_buffer(&self, event: &mut MathAstEventBuffer) {
        todo!()
    }

    fn exec(self, sheet: &mut LxAstSheet) -> Self::Outcome {
        // let LxAstData::TextEdit { ref buffer } = sheet.arena[self.ast_idx] else {
        //     unreachable!()
        // };
        todo!()
    }
}
