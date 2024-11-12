#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")] // hide console window on Windows in release
#![allow(rustdoc::missing_crate_level_docs)] // it's an example

use eframe::egui;
use egui::*;
use ui::hotkey::egui::{HotkeyBuffer, HotkeyMap};

fn main() -> eframe::Result {
    env_logger::init(); // Log to stderr (if you run with `RUST_LOG=debug`).
    let options = eframe::NativeOptions::default();
    eframe::run_native(
        "Keyboard events",
        options,
        Box::new(|_cc| Ok(Box::<Content>::default())),
    )
}

#[derive(Debug, Clone, Copy)]
pub enum Action {
    Jump,
    Run,
    Sit,
    Alt8,
}

struct Content {
    hotkey_buffer: HotkeyBuffer,
    hotkey_map: HotkeyMap<Action>,
    text1: String,
    text2: String,
    last_action: Option<Action>,
}

impl Default for Content {
    fn default() -> Self {
        use Action::*;

        Self {
            hotkey_buffer: Default::default(),
            hotkey_map: HotkeyMap::new([("R", Run), ("S", Sit), ("J", Jump), ("Alt+8", Alt8)])
                .unwrap(),
            text1: Default::default(),
            text2: Default::default(),
            last_action: None,
        }
    }
}

impl eframe::App for Content {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        self.hotkey_buffer.start_frame(ctx);
        egui::CentralPanel::default().show(ctx, |ui| {
            use husky_print_utils::p;

            if let Some((_, action)) = self.hotkey_buffer.extract(&self.hotkey_map) {
                self.last_action = Some(action);
            }
            match self.last_action {
                Some(action) => ui.label(format!("Action = {:?}", action)),
                None => ui.label(format!("Action = None")),
            };
            let edit2 = ui.text_edit_singleline(&mut self.text2);
            if edit2.has_focus() {
                self.hotkey_buffer.set_intercept_for_text_edit()
            }
            ctx.input(|i| {
                use husky_print_utils::p;
                for event in &i.events {
                    match event {
                        Event::Text(t) => {
                            println!("{}", t);
                        }
                        _ => (),
                    }
                }
            });
        });
    }
}
