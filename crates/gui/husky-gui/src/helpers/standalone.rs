use ui::{component::ComponentUi, hotkey::egui::HotkeyBuffer};

pub fn run_standalone_ui_component<UiComponent, UiComponentConfig, UiActionBuffer>(
    component: UiComponent,
    settings: UiComponentConfig,
    action_buffer: UiActionBuffer,
) -> Result<(), eframe::Error>
where
    UiComponent: ComponentUi<egui::Ui, UiComponentConfig, UiActionBuffer> + 'static,
    UiComponentConfig: 'static,
    UiActionBuffer: 'static,
{
    let options = eframe::NativeOptions {
        // initial_window_size: Some(egui::vec2(320.0, 240.0)),
        ..Default::default()
    };
    eframe::run_native(
        "Standalone Ui Component",
        options,
        Box::new(|_cc| {
            Ok(Box::new(StandaloneUiApp {
                component,
                hotkey_buffer: Default::default(),
                settings,
                action_buffer,
            }))
        }),
    )
}

struct StandaloneUiApp<UiComponent, UiComponentSettings, UiActionBuffer> {
    component: UiComponent,
    settings: UiComponentSettings,
    hotkey_buffer: HotkeyBuffer,
    action_buffer: UiActionBuffer,
}

impl<UiComponent, UiComponentConfig, UiActionBuffer> eframe::App
    for StandaloneUiApp<UiComponent, UiComponentConfig, UiActionBuffer>
where
    UiComponent: ComponentUi<egui::Ui, UiComponentConfig, UiActionBuffer>,
{
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        egui::CentralPanel::default().show(ctx, |ui| {
            self.component.component_ui(
                &mut self.settings,
                &mut self.hotkey_buffer,
                &mut self.action_buffer,
                ui,
            )
        });
    }
}
