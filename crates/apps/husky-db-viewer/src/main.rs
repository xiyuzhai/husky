use eframe::egui;
use rfd::FileDialog;
use rusqlite::{Connection, Result};
use std::path::PathBuf;

struct DbVisualizerApp {
    db_path: Option<PathBuf>,
    conn: Option<Connection>,
    tables: Vec<String>,
    selected_table: Option<String>,
    table_data: Vec<Vec<String>>,
}

impl Default for DbVisualizerApp {
    fn default() -> Self {
        Self {
            db_path: None,
            conn: None,
            tables: Vec::new(),
            selected_table: None,
            table_data: Vec::new(),
        }
    }
}

impl eframe::App for DbVisualizerApp {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        egui::CentralPanel::default().show(ctx, |ui| {
            if ui.button("Open SQLite Database").clicked() {
                if let Some(path) = FileDialog::new()
                    .add_filter("SQLite Database", &["db", "sqlite", "sqlite3"])
                    .pick_file()
                {
                    self.open_database(path);
                }
            }

            if let Some(ref path) = self.db_path {
                ui.label(format!("Opened Database: {}", path.display()));

                if !self.tables.is_empty() {
                    egui::ComboBox::from_label("Select Table")
                        .selected_text(
                            self.selected_table
                                .clone()
                                .unwrap_or_else(|| "Select a table".to_string()),
                        )
                        .show_ui(ui, |combo_ui| {
                            let mut changed = false;
                            for table in &self.tables {
                                if combo_ui
                                    .selectable_value(
                                        &mut self.selected_table,
                                        Some(table.clone()),
                                        table,
                                    )
                                    .changed()
                                {
                                    changed = true;
                                }
                            }
                            if changed {
                                self.load_table_data();
                            }
                        });
                }

                if !self.table_data.is_empty() {
                    egui::ScrollArea::vertical().show(ui, |ui| {
                        for row in &self.table_data {
                            ui.horizontal(|ui| {
                                for cell in row {
                                    ui.label(cell);
                                }
                            });
                        }
                    });
                }
            }
        });
    }
}

impl DbVisualizerApp {
    fn open_database(&mut self, path: PathBuf) {
        match Connection::open(&path) {
            Ok(conn) => {
                self.db_path = Some(path);
                self.conn = Some(conn);
                self.load_tables();
            }
            Err(err) => {
                eprintln!("Failed to open database: {}", err);
            }
        }
    }

    fn load_tables(&mut self) {
        if let Some(ref conn) = self.conn {
            let mut stmt = match conn.prepare("SELECT name FROM sqlite_master WHERE type='table'") {
                Ok(stmt) => stmt,
                Err(err) => {
                    eprintln!("Failed to query tables: {}", err);
                    return;
                }
            };

            let table_iter = match stmt.query_map([], |row| row.get(0)) {
                Ok(iter) => iter,
                Err(err) => {
                    eprintln!("Failed to iterate tables: {}", err);
                    return;
                }
            };

            self.tables.clear();
            for table_name in table_iter {
                if let Ok(name) = table_name {
                    self.tables.push(name);
                }
            }
        }
    }

    fn load_table_data(&mut self) {
        if let (Some(ref conn), Some(ref table_name)) = (&self.conn, &self.selected_table) {
            let query = format!("SELECT * FROM {}", table_name);
            let mut stmt = match conn.prepare(&query) {
                Ok(stmt) => stmt,
                Err(err) => {
                    eprintln!("Failed to prepare query: {}", err);
                    return;
                }
            };

            let column_count = stmt.column_count();

            let data_iter = match stmt.query_map([], |row| {
                let mut row_data = Vec::new();
                for i in 0..column_count {
                    row_data.push(
                        row.get::<_, String>(i)
                            .unwrap_or_else(|_| "NULL".to_string()),
                    );
                }
                Ok(row_data)
            }) {
                Ok(iter) => iter,
                Err(err) => {
                    eprintln!("Failed to execute query: {}", err);
                    return;
                }
            };

            self.table_data.clear();
            for row in data_iter {
                if let Ok(data) = row {
                    self.table_data.push(data);
                }
            }
        }
    }
}

fn main() -> Result<()> {
    let options = eframe::NativeOptions::default();
    eframe::run_native(
        "SQLite Database Visualizer",
        options,
        Box::new(|_cc| Ok(Box::new(DbVisualizerApp::default()))),
    );
    Ok(())
}
