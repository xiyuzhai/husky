use super::{action::text_edit::MathAstTextEditAction, LxAstSheetTimeCapsule};
use crate::ast::{math::LxMathAstData, rose::LxRoseAstData, LxAstData, LxAstIdx};

pub struct LxAstSheetView<'a> {
    time_capsule: &'a mut LxAstSheetTimeCapsule,
}

pub struct LxAstView<'a> {
    ast_idx: LxAstIdx,
    time_capsule: &'a mut LxAstSheetTimeCapsule,
}

impl<'a> LxAstView<'a> {
    pub fn ui(self, ui: &mut egui::Ui) {
        match self.ast_idx {
            LxAstIdx::Math(idx) => match self.time_capsule.arena().math[idx] {
                LxMathAstData::TextEdit { .. } => self.time_capsule.add_event(|event_builder| {
                    event_builder.add_action(MathAstTextEditAction::new(idx, |text| {
                        ui.text_edit_singleline(text);
                    }))
                }),
                _ => todo!(),
            },
            LxAstIdx::Rose(idx) => match self.time_capsule.arena().rose[idx] {
                LxRoseAstData::TextEdit { .. } => todo!(),
                _ => todo!(),
            },
            LxAstIdx::Lisp(arena_idx) => todo!(),
            LxAstIdx::Root(arena_idx) => todo!(),
        }
    }
}
