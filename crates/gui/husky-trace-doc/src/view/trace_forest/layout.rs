mod amazon;
mod congo;
mod guinea;
mod taiga;

use super::*;
impl<'a, TraceProtocol, Settings> TraceDocView<'a, TraceProtocol, Settings>
where
    TraceProtocol: IsTraceProtocol,

    TraceProtocol::Figure: FigureUi<egui::Ui>,
    Settings: HasTraceDocSettings,
{
    pub(crate) fn forest_ui(&mut self, ui: &mut egui::Ui) {
        // todo: use layout style to determine
        self.amazon_trace_forest_ui(ui)
    }
}
