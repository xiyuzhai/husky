pub mod action;
mod app;
mod components;
mod doc;
mod facade;
mod settings;

use std::sync::Arc;

use self::action::*;
use self::app::*;
use self::doc::{DocTab, Docs};
use self::settings::*;
use eframe::egui;
use ui::hotkey::egui::HotkeyBuffer;

fn main() -> Result<(), eframe::Error> {
    tracing_subscriber::fmt::init();

    let options = eframe::NativeOptions {
        // initial_window_size: Some(egui::vec2(320.0, 240.0)),
        ..Default::default()
    };
    eframe::run_native(
        "Husky Notebook",
        options,
        Box::new(|_cc| Ok(Box::new(NotebookApp::default()))),
    )
}
