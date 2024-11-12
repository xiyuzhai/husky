use super::*;

pub(in crate::sheet) struct MathAstAllocAstAction {
    ast_data: LxMathAstData,
}

impl MathAstAllocAstAction {
    pub(in crate::sheet) fn new(ast_data: LxMathAstData) -> Self {
        Self { ast_data }
    }
}

impl IsTimeCapsuleAction for MathAstAllocAstAction {
    type Event = MathAstEvent;

    type Outcome = LxMathAstIdx;

    fn add_to_event_buffer(&self, _event: &mut MathAstEventBuffer) {
        // ignored because sheet is append only, no need to undo
        ()
    }

    fn exec(self, sheet: &mut LxAstSheet) -> Self::Outcome {
        sheet.alloc_math_ast(self.ast_data)
    }
}
