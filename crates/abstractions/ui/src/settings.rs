#[cfg(feature = "egui")]
pub mod egui;

use crate::ui::IsUi;

pub trait SettingsUi<Ui: IsUi> {
    fn for_each_section(&mut self, f: &mut dyn FnMut(&str, &mut dyn SettingSectionUi<Ui>));
}

/// trivial implementation
impl<Ui: IsUi> SettingsUi<Ui> for () {
    fn for_each_section(&mut self, _f: &mut dyn FnMut(&str, &mut dyn SettingSectionUi<Ui>)) {}
}

pub trait SettingSectionUi<Ui: IsUi> {
    fn for_each_subsection(&mut self, f: &mut dyn FnMut(&str, &mut dyn SettingSubsectionUi<Ui>));
}

/// trivial implementation
impl<Ui: IsUi> SettingSectionUi<Ui> for () {
    fn for_each_subsection(&mut self, f: &mut dyn FnMut(&str, &mut dyn SettingSubsectionUi<Ui>)) {}
}

pub trait SettingSubsectionUi<Ui: IsUi> {
    fn for_each_item(&mut self, f: &mut dyn FnMut(&str, &mut dyn SettingItemUi<Ui>));
}

/// trivial implementation
impl<Ui: IsUi> SettingSubsectionUi<Ui> for () {
    fn for_each_item(&mut self, f: &mut dyn FnMut(&str, &mut dyn SettingItemUi<Ui>)) {}
}

pub trait SettingItemUi<Ui: IsUi> {
    fn setting_item_ui(&mut self, item_title: &str, ui: &mut Ui);
}

/// trivial implementation
impl SettingItemUi<()> for () {
    fn setting_item_ui(&mut self, _item_title: &str, _ui: &mut ()) {}
}

impl SettingItemUi<()> for bool {
    fn setting_item_ui(&mut self, _item_title: &str, _ui: &mut ()) {}
}

impl SettingItemUi<()> for u32 {
    fn setting_item_ui(&mut self, _item_title: &str, _ui: &mut ()) {}
}

impl SettingItemUi<()> for f32 {
    fn setting_item_ui(&mut self, _item_title: &str, _ui: &mut ()) {}
}

impl SettingItemUi<()> for String {
    fn setting_item_ui(&mut self, _item_title: &str, _ui: &mut ()) {}
}
