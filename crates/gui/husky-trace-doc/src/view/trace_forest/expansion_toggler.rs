use super::*;
use egui::{Response, Ui};

impl<'a, TraceProtocol, Settings> TraceDocView<'a, TraceProtocol, Settings>
where
    TraceProtocol: IsTraceProtocol,
    Settings: HasTraceDocSettings,
{
    pub(in super::super) fn render_expansion_toggler(
        &mut self,
        trace_id: TraceId,
        have_subtraces: bool,
        expanded: bool,
        ui: &mut Ui,
    ) {
        // render prefix
        let toggler_width = self.glyph_width * 1.5;
        if have_subtraces {
            let button_response = self.render_expansion_toggler_inner(trace_id, expanded, ui);
            ui.allocate_space(Vec2::new(
                toggler_width - button_response.rect.width() - 2.0, // 2.0 is equal to item spacing
                button_response.rect.height(),
            ));
        } else {
            ui.allocate_space(Vec2::new(toggler_width, 0.));
        }
    }

    fn render_expansion_toggler_inner(
        &mut self,
        trace_id: TraceId,
        expanded: bool,
        ui: &mut Ui,
    ) -> Response {
        // todo: different styles
        let symbol_style = ExpansionTogglerSymbolStyle::PlusMinus;
        ui.style_mut().visuals.widgets.inactive.fg_stroke.color = Color32::from_gray(55);
        ui.style_mut().visuals.widgets.hovered.fg_stroke.color = Color32::from_gray(155);
        let toggler =
            Label::new(RichText::new(symbol_style.text(expanded)).family(FontFamily::Monospace))
                .sense(Sense::click())
                .selectable(false)
                .ui(ui);
        if toggler.clicked() {
            self.add_action(TraceViewAction::ToggleExpansion { trace_id })
        };
        toggler
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Hash)]
pub enum ExpansionTogglerSymbolStyle {
    PlusMinus,
    ConcreteArrowHead,
}

impl ExpansionTogglerSymbolStyle {
    fn text(&self, expanded: bool) -> &str {
        match self {
            ExpansionTogglerSymbolStyle::PlusMinus => match expanded {
                true => "-",
                false => "+",
            },
            ExpansionTogglerSymbolStyle::ConcreteArrowHead => match expanded {
                true => "⏷",
                false => "⏵",
            },
        }
    }
}
