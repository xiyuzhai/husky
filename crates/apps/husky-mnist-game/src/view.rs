pub mod components;
pub mod layout;

use crate::*;

impl eframe::App for MnistApp {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        self.layout(ctx);
    }
}
