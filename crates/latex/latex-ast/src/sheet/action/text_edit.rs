use super::*;
use crate::ast::{math::LxMathAstData, rose::LxRoseAstData};

pub(in crate::sheet) struct MathAstTextEditAction<F>
where
    F: FnOnce(&mut String),
{
    ast_idx: LxMathAstIdx,
    f: F,
}

impl<F> MathAstTextEditAction<F>
where
    F: FnOnce(&mut String),
{
    pub(in crate::sheet) fn new(ast_idx: LxMathAstIdx, f: F) -> Self {
        Self { ast_idx, f }
    }
}

impl<F> IsTimeCapsuleAction for MathAstTextEditAction<F>
where
    F: FnOnce(&mut String),
{
    type Event = MathAstEvent;

    type Outcome = ();

    fn add_to_event_buffer(&self, _event: &mut MathAstEventBuffer) {
        // ignored because text editing is too trivial to be recorded
        ()
    }

    fn exec(self, sheet: &mut LxAstSheet) -> Self::Outcome {
        sheet.arena.math.update(self.ast_idx, |ast| match ast {
            LxMathAstData::TextEdit { ref mut buffer, .. } => (self.f)(buffer),
            _ => unreachable!(),
        })
    }
}

#[test]
fn math_ast_text_edit_action_works() {
    let mut sheet: LxAstSheet = Default::default();
    let ast_idx = sheet.alloc_math_ast(
        LxMathAstData::TextEdit {
            buffer: "hello,".to_string(),
        }
        .into(),
    );
    let action = MathAstTextEditAction::new(ast_idx, |s| *s += " world");
    action.exec(&mut sheet);
    let LxMathAstData::TextEdit { ref buffer, .. } = sheet.arena.math[ast_idx] else {
        unreachable!()
    };
    assert_eq!(buffer, "hello, world")
}
