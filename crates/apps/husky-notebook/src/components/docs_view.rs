use super::*;
use egui::{vec2, Color32};
use ui::hotkey::egui::HotkeyBuffer;

impl NotebookApp {
    pub(crate) fn render_docs_view(&mut self, ui: &mut egui::Ui) {
        let mut style = egui_dock::Style::from_egui(ui.style().as_ref());
        style.main_surface_border_stroke.width = 0.0;
        style.main_surface_border_stroke.color = Color32::KHAKI;
        style.tab.tab_body.inner_margin = 0.0.into();
        style.main_surface_border_rounding = 0.0.into();
        style.tab.tab_body.stroke.width = 0.0;
        // style.tab_bar.bg_fill = Color32::RED;
        egui_dock::DockArea::new(&mut self.dock_state)
            .style(style)
            .show_inside(
                ui,
                &mut DocsView {
                    docs: &mut self.docs,
                    settings: &mut self.settings,
                    hotkey_buffer: &mut self.hotkey_buffer,
                    action_buffer: &mut self.action_buffer,
                },
            )
    }
}

struct DocsView<'a> {
    docs: &'a mut Docs,
    settings: &'a mut NotebookSettings,
    hotkey_buffer: &'a mut HotkeyBuffer,
    action_buffer: &'a mut NotebookActionBuffer,
}

impl<'a> egui_dock::TabViewer for DocsView<'a> {
    type Tab = DocTab;

    fn ui(&mut self, ui: &mut egui::Ui, tab: &mut Self::Tab) {
        ui.style_mut().spacing.item_spacing = vec2(0.0, 0.0);
        self.action_buffer.with_doc_id(tab.id(), |action_buffer| {
            self.docs.component_mut(tab.id()).component_ui(
                self.settings,
                self.hotkey_buffer,
                action_buffer,
                ui,
            )
        });
    }

    fn title(&mut self, tab: &mut Self::Tab) -> egui::WidgetText {
        self.docs.doc_arena()[tab.id()].title().into()
    }

    fn scroll_bars(&self, _tab: &Self::Tab) -> [bool; 2] {
        [false, false]
    }
}
