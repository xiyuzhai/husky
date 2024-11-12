use crate::test_helpers::egui::launch_test_app;
use ::ui::{settings::*, ui::*, *};
use eframe::egui;

#[derive(SettingsUi)]
struct VsCodeSettings {
    editor: EditorSettings,
    workbench: WorkbenchSettings,
    terminal: TerminalSettings,
}

#[derive(SettingSectionUi)]
struct EditorSettings {
    font: FontSettings,
    cursor: CursorSettings,
    find: FindSettings,
}

#[derive(SettingSubsectionUi)]
struct FontSettings {
    size: u32,
    family: String,
    line_height: f32,
}

#[derive(SettingSubsectionUi)]
struct CursorSettings {
    style: String,
    blink: bool,
    width: u32,
}

#[derive(SettingSubsectionUi)]
struct FindSettings {
    case_sensitive: bool,
    whole_word: bool,
    regex: bool,
}

#[derive(SettingSectionUi)]
struct WorkbenchSettings {
    appearance: AppearanceSettings,
    sidebar: SidebarSettings,
}

#[derive(SettingSubsectionUi)]
struct AppearanceSettings {
    color_theme: String,
    icon_theme: String,
}

#[derive(SettingSubsectionUi)]
struct SidebarSettings {
    position: String,
    visible: bool,
}

#[derive(SettingSectionUi)]
struct TerminalSettings {
    integrated: IntegratedTerminalSettings,
}

#[derive(SettingSubsectionUi)]
struct IntegratedTerminalSettings {
    shell_windows: String,
    shell_linux: String,
    shell_osx: String,
}

#[test]
fn vscode_settings_trivial_ui_test() {
    let mut settings = VsCodeSettings {
        editor: EditorSettings {
            font: FontSettings {
                size: 14,
                family: "Consolas".to_string(),
                line_height: 1.5,
            },
            cursor: CursorSettings {
                style: "line".to_string(),
                blink: true,
                width: 2,
            },
            find: FindSettings {
                case_sensitive: false,
                whole_word: false,
                regex: false,
            },
        },
        workbench: WorkbenchSettings {
            appearance: AppearanceSettings {
                color_theme: "Monokai".to_string(),
                icon_theme: "vs-seti".to_string(),
            },
            sidebar: SidebarSettings {
                position: "left".to_string(),
                visible: true,
            },
        },
        terminal: TerminalSettings {
            integrated: IntegratedTerminalSettings {
                shell_windows: "C:\\Windows\\System32\\WindowsPowerShell\\v1.0\\powershell.exe"
                    .to_string(),
                shell_linux: "/bin/bash".to_string(),
                shell_osx: "/bin/zsh".to_string(),
            },
        },
    };

    let mut sections = Vec::new();
    let mut subsections = Vec::new();
    let mut items = Vec::new();

    settings.for_each_section(&mut |section_title, section| {
        sections.push(section_title.to_string());
        section.for_each_subsection(&mut |subsection_title, subsection| {
            subsections.push(subsection_title.to_string());
            subsection.for_each_item(&mut |item_title, item| {
                items.push(item_title.to_string());
                item.setting_item_ui(item_title, &mut ());
            });
        });
    });

    assert_eq!(sections, vec!["Editor", "Workbench", "Terminal"]);
    assert_eq!(
        subsections,
        vec![
            "Font",
            "Cursor",
            "Find",
            "Appearance",
            "Sidebar",
            "Integrated"
        ]
    );
    assert_eq!(
        items,
        vec![
            "Size",
            "Family",
            "Line height",
            "Style",
            "Blink",
            "Width",
            "Case sensitive",
            "Whole word",
            "Regex",
            "Color theme",
            "Icon theme",
            "Position",
            "Visible",
            "Shell windows",
            "Shell linux",
            "Shell osx"
        ]
    );

    // Additional assertions can be added here if needed
}

fn main() {
    let mut settings = VsCodeSettings {
        editor: EditorSettings {
            font: FontSettings {
                size: 14,
                family: "Consolas".to_string(),
                line_height: 1.5,
            },
            cursor: CursorSettings {
                style: "line".to_string(),
                blink: true,
                width: 2,
            },
            find: FindSettings {
                case_sensitive: false,
                whole_word: false,
                regex: false,
            },
        },
        workbench: WorkbenchSettings {
            appearance: AppearanceSettings {
                color_theme: "Monokai".to_string(),
                icon_theme: "vs-seti".to_string(),
            },
            sidebar: SidebarSettings {
                position: "left".to_string(),
                visible: true,
            },
        },
        terminal: TerminalSettings {
            integrated: IntegratedTerminalSettings {
                shell_windows: "C:\\Windows\\System32\\WindowsPowerShell\\v1.0\\powershell.exe"
                    .to_string(),
                shell_linux: "/bin/bash".to_string(),
                shell_osx: "/bin/zsh".to_string(),
            },
        },
    };

    launch_test_app(move |ui| {
        settings.for_each_section(&mut |section_title, section| {
            ui.collapsing(section_title, |ui| {
                section.for_each_subsection(&mut |subsection_title, subsection| {
                    ui.collapsing(subsection_title, |ui| {
                        subsection.for_each_item(&mut |item_title, item| {
                            item.setting_item_ui(item_title, ui);
                        });
                    });
                });
            });
        });
    });
}
