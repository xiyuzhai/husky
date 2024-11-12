use super::*;
use ui::hotkey::egui::{HotkeyMap, HotkeyPattern};

#[derive(PartialEq, Eq)]
pub struct NotebookHotkeySettings {
    main_hotkey_map: HotkeyMap<NotebookHotkeyAction>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum NotebookHotkeyAction {
    ToggleHelpFacade,
    ToggleDocHelpFacade,
}

impl Default for NotebookHotkeySettings {
    fn default() -> Self {
        Self {
            main_hotkey_map: HotkeyMap::new([
                ("Ctrl+Shift+H", NotebookHotkeyAction::ToggleHelpFacade),
                ("Ctrl+h", NotebookHotkeyAction::ToggleDocHelpFacade),
            ])
            .unwrap(),
        }
    }
}

impl NotebookSettings {
    pub(crate) fn hotkey_map(
        &self,
    ) -> impl Iterator<Item = (&HotkeyPattern, NotebookHotkeyAction)> {
        self.hotkey.hotkey_map()
    }
}

impl NotebookHotkeySettings {
    fn hotkey_map(&self) -> impl Iterator<Item = (&HotkeyPattern, NotebookHotkeyAction)> {
        self.main_hotkey_map.into_iter()
    }
}
