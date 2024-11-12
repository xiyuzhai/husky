use super::*;

pub(in crate::sheet) struct MathAstAllocAstAction {
    asts_data: Vec<LxMathAstData>,
}

impl MathAstAllocAstAction {
    pub(in crate::sheet) fn new(asts_data: Vec<LxMathAstData>) -> Self {
        Self { asts_data }
    }
}

impl IsTimeCapsuleAction for MathAstAllocAstAction {
    type Event = MathAstEvent;

    type Outcome = LxMathAstIdxRange;

    fn add_to_event_buffer(&self, _event: &mut MathAstEventBuffer) {
        // ignored because sheet is append only, no need to undo
        ()
    }

    fn exec(self, sheet: &mut LxAstSheet) -> Self::Outcome {
        sheet.alloc_math_asts(self.asts_data)
    }
}
