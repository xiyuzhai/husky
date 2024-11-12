use super::*;

impl<'a, TraceProtocol, Settings> TraceDocView<'a, TraceProtocol, Settings>
where
    TraceProtocol: IsTraceProtocol,
    Settings: HasTraceDocSettings,
{
    pub(in super::super) fn render_value(&self, value: &ValuePresentation, ui: &mut egui::Ui)
    where
        TraceProtocol: IsTraceProtocol,
    {
        self.render_space_chars(1, ui);
        match value {
            ValuePresentation::Unit(()) => {
                ui.label(format!("()"));
            }
            ValuePresentation::Bool(b) => {
                ui.label(format!("{}", b));
            }
            ValuePresentation::Char(c) => {
                ui.label(format!("'{}'", c));
            }
            ValuePresentation::I8(i) => {
                ui.label(format!("{}i8", i));
            }
            ValuePresentation::I16(i) => {
                ui.label(format!("{}i16", i));
            }
            ValuePresentation::I32(i) => {
                ui.label(format!("{}i32", i));
            }
            ValuePresentation::I64(i) => {
                ui.label(format!("{}i64", i));
            }
            ValuePresentation::I128(i) => {
                ui.label(format!("{}i128", i));
            }
            ValuePresentation::ISize(i) => {
                ui.label(format!("{}isize", i));
            }
            ValuePresentation::U8(u) => {
                ui.label(format!("{}u8", u));
            }
            ValuePresentation::U16(u) => {
                ui.label(format!("{}u16", u));
            }
            ValuePresentation::U32(u) => {
                ui.label(format!("{}u32", u));
            }
            ValuePresentation::U64(u) => {
                ui.label(format!("{}u64", u));
            }
            ValuePresentation::U128(u) => {
                ui.label(format!("{}u128", u));
            }
            ValuePresentation::USize(u) => {
                ui.label(format!("{}usize", u));
            }
            ValuePresentation::R8(r) => {
                ui.label(format!("{}r8", r));
            }
            ValuePresentation::R16(r) => {
                ui.label(format!("{}r16", r));
            }
            ValuePresentation::R32(r) => {
                ui.label(format!("{}r32", r));
            }
            ValuePresentation::R64(r) => {
                ui.label(format!("{}r64", r));
            }
            ValuePresentation::R128(r) => {
                ui.label(format!("{}r128", r));
            }
            ValuePresentation::RSize(r) => {
                ui.label(format!("{}rsize", r));
            }
            ValuePresentation::F32(f) => {
                ui.label(format!("{}f32", f));
            }
            ValuePresentation::F64(f) => {
                ui.label(format!("{}f64", f));
            }
            ValuePresentation::Enum => todo!(),
            ValuePresentation::Struct => todo!(),
            ValuePresentation::AdHoc(s) => {
                // ad hoc
                if s.len() > 30 {
                    ui.label(format!("{}...", &s[..30]));
                } else {
                    ui.label(s);
                }
            }
        }
    }
}
