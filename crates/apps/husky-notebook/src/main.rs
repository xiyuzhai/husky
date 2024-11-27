pub mod action;
mod app;
mod components;
mod doc;
mod facade;
mod settings;

use self::action::*;
use self::app::*;
use self::doc::{DocTab, Docs};
use self::settings::*;
use clap::Parser;
use eframe::egui;
use husky_session::Session;
use std::path::PathBuf;
use std::sync::Arc;
use ui::hotkey::egui::HotkeyBuffer;

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    /// Path to the session YAML file
    #[arg(long)]
    session: Option<PathBuf>,
}

fn main() -> Result<(), eframe::Error> {
    tracing_subscriber::fmt::init();

    let options = eframe::NativeOptions {
        // initial_window_size: Some(egui::vec2(320.0, 240.0)),
        ..Default::default()
    };
    let cli = Cli::parse();
    let session = if let Some(session_path) = cli.session {
        Session::load_from_yaml_file_path(&session_path)
    } else {
        todo!()
    };
    eframe::run_native(
        "Husky Notebook",
        options,
        Box::new(|_cc| Ok(Box::new(NotebookApp::new(session)))),
    )
}
