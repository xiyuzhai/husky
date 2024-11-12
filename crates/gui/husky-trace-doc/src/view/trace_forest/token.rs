use egui::CursorIcon;

use super::*;

impl<'a, TraceProtocol, Settings> TraceDocView<'a, TraceProtocol, Settings>
where
    TraceProtocol: IsTraceProtocol,
    Settings: HasTraceDocSettings,
{
    pub(in super::super) fn render_token(
        &mut self,
        token_data: &TraceViewTokenData,
        trace_id: TraceId,
        entry: &TraceSynchrotronEntry<TraceProtocol>,
        ui: &mut egui::Ui,
    ) {
        let token_foreground_colors = self
            .settings
            .code_editor_settings()
            .token_foreground_colors();
        let spaces_before = token_data.spaces_before();
        self.render_space_chars(spaces_before, ui);
        let mut label = Label::new(
            RichText::new(token_data.text())
                .family(FontFamily::Monospace)
                .color(token_foreground_colors[token_data.token_class()]),
        )
        .selectable(false);
        if token_data.assoc_trace_id().is_some() {
            label = label.sense(Sense::click());
        }
        let label_response = label.ui(ui);
        if let Some(assoc_trace_id) = token_data.assoc_trace_id() {
            if label_response.clicked() {
                self.add_action(TraceViewAction::ToggleAssocTrace {
                    trace_id,
                    assoc_trace_id,
                })
            }
            if entry.assoc_trace_ids().contains(&assoc_trace_id) {
                label_response.highlight();
            } else if label_response.hovered() {
                label_response.highlight();
            }
        }
    }
}
