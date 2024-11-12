pub mod doc;
pub mod frame;
pub mod hotkey;
pub mod layout;

pub(crate) use self::doc::*;
pub(crate) use self::layout::*;

use egui::Color32;
use hotkey::NotebookHotkeySettings;
use husky_code_editor::settings::HasCodeEditorSettings;
use husky_trace_doc::settings::HasTraceDocSettings;
use husky_trace_protocol::settings::HasTraceSettings;
use ui::{component::ComponentUi, hotkey::egui::HotkeyBuffer};

#[derive(Default, PartialEq, Eq)]
pub(crate) struct NotebookSettings {
    layout: HuskyNotebookLayoutSettings,
    doc: HuskyNotebookDocSettings,
    hotkey: NotebookHotkeySettings,
}

impl HasCodeEditorSettings for NotebookSettings {
    fn code_editor_settings(&self) -> &husky_code_editor::settings::CodeEditorSettings {
        self.doc.code_editor_settings()
    }
}

impl HasTraceSettings for NotebookSettings {
    fn trace_settings(&self) -> &husky_trace_protocol::settings::TraceSettings {
        self.doc.trace_settings()
    }
}

impl HasTraceDocSettings for NotebookSettings {
    fn trace_doc_settings(&self) -> &husky_trace_doc::settings::TraceDocSettings {
        todo!()
    }

    fn trace_doc_settings_mut(&mut self) -> &mut husky_trace_doc::settings::TraceDocSettings {
        todo!()
    }
}

pub(crate) struct NotebookSettingsView;

impl<ParentActionBuffer> ComponentUi<egui::Ui, NotebookSettings, ParentActionBuffer>
    for NotebookSettingsView
{
    fn component_ui(
        &mut self,
        _settings: &mut NotebookSettings,
        hotkey_buffer: &mut HotkeyBuffer,
        _super_action_buffer: &mut ParentActionBuffer,
        ui: &mut egui::Ui,
    ) {
        ui.label("Ui Component Context");
    }

    fn toggle_help_facade(&mut self) {
        todo!()
    }
}
