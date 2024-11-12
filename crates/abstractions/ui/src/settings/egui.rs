use super::*;

/// trivial implementation
impl SettingItemUi<::egui::Ui> for () {
    fn setting_item_ui(&mut self, item_title: &str, ui: &mut ::egui::Ui) {}
}

impl SettingItemUi<::egui::Ui> for bool {
    fn setting_item_ui(&mut self, item_title: &str, ui: &mut ::egui::Ui) {
        ui.checkbox(self, item_title);
    }
}

impl SettingItemUi<::egui::Ui> for u32 {
    fn setting_item_ui(&mut self, item_title: &str, ui: &mut ::egui::Ui) {
        ui.add(::egui::Slider::new(self, 0..=100).text(item_title));
    }
}

impl SettingItemUi<::egui::Ui> for f32 {
    fn setting_item_ui(&mut self, item_title: &str, ui: &mut ::egui::Ui) {
        ui.add(::egui::Slider::new(self, 0.0..=1.0).text(item_title));
    }
}

impl SettingItemUi<::egui::Ui> for String {
    fn setting_item_ui(&mut self, item_title: &str, ui: &mut ::egui::Ui) {
        ui.horizontal(|ui| {
            ui.label(item_title);
            ui.text_edit_singleline(self);
        });
    }
}
