use super::*;
use egui::Ui;

impl<'a, TraceProtocol, Settings> TraceDocView<'a, TraceProtocol, Settings>
where
    TraceProtocol: IsTraceProtocol,
    Settings: HasTraceDocSettings,
{
    pub(in super::super) fn render_accompany_toggler(
        &mut self,
        trace_id: TraceId,
        accompanied: bool,
        ui: &mut Ui,
    ) {
        let symbol_style = AccompanyTogglerSymbolStyle::RedPin;
        let color: Color32 = match accompanied {
            true => Color32::from_gray(200),
            false => Color32::from_gray(55),
        };
        let toggler = Label::new(
            RichText::new(symbol_style.text())
                .family(FontFamily::Monospace)
                .color(color),
        )
        .sense(Sense::click())
        .selectable(false)
        .ui(ui);
        if toggler.clicked() {
            self.add_action(TraceViewAction::ToggleAccompany { trace_id })
        }
    }
}

pub enum AccompanyTogglerSymbolStyle {
    RedPin,
}

impl AccompanyTogglerSymbolStyle {
    fn text(&self) -> &str {
        match self {
            AccompanyTogglerSymbolStyle::RedPin => "📌",
        }
    }
}
