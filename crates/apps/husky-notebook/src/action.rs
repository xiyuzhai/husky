use ui::app::IsParentActionBuffer;

use crate::{doc::arena::DocId, hotkey::NotebookHotkeyAction, NotebookApp};

pub enum NotebookAction {
    ToggleHelpFacade,
    ToggleDocHelpFacade,
    Concentracte { doc_id: DocId },
}

impl NotebookAction {
    pub(crate) fn from_hotkey_action(
        argument: Option<usize>,
        action: NotebookHotkeyAction,
    ) -> Self {
        match action {
            NotebookHotkeyAction::ToggleHelpFacade => NotebookAction::ToggleHelpFacade,
            NotebookHotkeyAction::ToggleDocHelpFacade => NotebookAction::ToggleDocHelpFacade,
        }
    }
}

#[derive(Default)]
pub struct NotebookActionBuffer {
    doc_id: Option<DocId>,
    actions: Vec<NotebookAction>,
}

impl NotebookActionBuffer {
    pub(crate) fn take_all(&mut self) -> Vec<NotebookAction> {
        std::mem::take(&mut self.actions)
    }

    pub(crate) fn with_doc_id(&mut self, doc_id: DocId, f: impl FnOnce(&mut Self)) {
        assert!(self.doc_id.is_none());
        self.doc_id = Some(doc_id);
        f(self);
        self.doc_id = None;
    }
}

impl IsParentActionBuffer for NotebookActionBuffer {
    fn concentrate(&mut self) {
        self.actions.push(NotebookAction::Concentracte {
            doc_id: self.doc_id.unwrap(),
        })
    }
}

impl NotebookApp {
    pub(crate) fn take_action(&mut self, action: NotebookAction) {
        match action {
            NotebookAction::ToggleHelpFacade => todo!(),
            NotebookAction::ToggleDocHelpFacade => {
                if let Some(id) = self.concentration {
                    self.docs.component_mut(id).toggle_help_facade()
                }
            }
            NotebookAction::Concentracte { doc_id } => todo!(),
        }
    }
}
