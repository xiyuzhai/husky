use super::*;

impl NotebookSettings {
    pub(crate) fn activity_bar_frame(&self) -> egui::Frame {
        egui::Frame::none()
    }

    pub(crate) fn log_view_frame(&self) -> egui::Frame {
        egui::Frame::none()
    }

    pub(crate) fn main_panel_frame(&self) -> egui::containers::Frame {
        egui::containers::Frame::default()
            .inner_margin(0.0)
            .fill(Color32::BLACK)
    }
}
