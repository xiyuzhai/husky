use super::*;
use egui::CentralPanel;

impl<'a, TraceProtocol, Settings> TraceDocView<'a, TraceProtocol, Settings>
where
    TraceProtocol: IsTraceProtocol,
    TraceProtocol::Figure: FigureUi<egui::Ui>,
    Settings: HasTraceDocSettings,
{
    pub(crate) fn render_figure_ocean(&mut self, ui: &mut egui::Ui) {
        let visual_synchrotron = self.trace_synchrotron.visual_synchrotron();
        if self.figures.is_empty() {
            ui.label("todo: empty figures");
        } else {
            let figures_len = self.figures.len();
            let total_available_width = ui.available_width();
            let side_panel_width = total_available_width / (figures_len as f32);
            // render all except last as side panels
            for figure in &self.figures[..(figures_len - 1)] {
                SidePanel::left(ui.auto_id_with("central_right"))
                    .frame(Frame::none().inner_margin(0.0))
                    .resizable(false)
                    .exact_width(side_panel_width)
                    .show_inside(ui, |ui| {
                        figure.figure_ui(visual_synchrotron, self.visual_ui_cache, ui)
                    });
            }
            CentralPanel::default().show_inside(ui, |ui| {
                self.figures
                    .last()
                    .unwrap()
                    .figure_ui(visual_synchrotron, self.visual_ui_cache, ui)
            });
        }
    }
}
