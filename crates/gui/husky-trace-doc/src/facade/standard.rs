use super::*;
use ::egui::*;
use husky_trace_protocol::{caryatid::CaryatidUi, figure::FigureUi, protocol::IsTraceProtocol};
use view::TraceDocView;

impl<'a, TraceProtocol, Settings> TraceDocView<'a, TraceProtocol, Settings>
where
    TraceProtocol: IsTraceProtocol,

    TraceProtocol::Figure: FigureUi<Ui>,
    TraceProtocol::Caryatid: CaryatidUi<Ui>,
    Settings: HasTraceDocSettings,
{
    pub(super) fn standard_facade_ui(mut self, ui: &mut egui::Ui) {
        TopBottomPanel::bottom(ui.next_auto_id())
            .frame(Frame::none().inner_margin(Margin {
                left: 2.0,
                right: 2.0,
                top: 4.0, // ad hoc, investigate the implementation of egui to understand why this is needed
                bottom: 2.0,
            }))
            .show_inside(ui, |ui| {
                ui.horizontal_centered(|ui| self.render_caryatid(ui))
            });
        self.central_region_ui(ui);
    }

    fn central_region_ui(&mut self, ui: &mut egui::Ui) {
        SidePanel::right(ui.auto_id_with("central_right"))
            .frame(Frame::none().inner_margin(0.0))
            .resizable(false)
            .exact_width(ui.available_width() / 1.618)
            .show_inside(ui, |ui| self.central_right_region_ui(ui));
        self.forest_ui(ui);
    }

    fn central_right_region_ui(&mut self, ui: &mut egui::Ui) {
        TopBottomPanel::bottom(ui.next_auto_id()).show_inside(ui, |ui| self.render_devtools(ui));
        CentralPanel::default().show_inside(ui, |ui| self.render_figure_ocean(ui));
    }
}
