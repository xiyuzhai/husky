use super::*;

use husky_trace_protocol::caryatid::CaryatidUi;

impl<'a, TraceProtocol, Settings> TraceDocView<'a, TraceProtocol, Settings>
where
    TraceProtocol: IsTraceProtocol,
    TraceProtocol::Caryatid: CaryatidUi<Ui>,
    Settings: HasTraceDocSettings,
{
    pub(crate) fn render_caryatid(&mut self, ui: &mut egui::Ui) {
        self.trace_synchrotron.caryatid().caryatid_ui(
            self.trace_synchrotron,
            ui,
            self.caryatid_ui_buffer,
            self.action_buffer,
        )
    }
}
