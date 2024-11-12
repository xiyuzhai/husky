use super::*;

impl<'a, TraceProtocol, Settings> TraceDocView<'a, TraceProtocol, Settings>
where
    TraceProtocol: IsTraceProtocol,
    Settings: HasTraceDocSettings,
{
    /// here space means the char ` `
    pub(super) fn render_space_chars(&self, n: u32, ui: &mut egui::Ui) {
        if n > 0 {
            ui.allocate_space(Vec2::new(self.glyph_width * (n as f32), 0.));
        }
    }
}
