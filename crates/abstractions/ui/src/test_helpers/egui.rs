use eframe::egui;

pub fn launch_test_app<F>(f: F)
where
    F: FnMut(&mut egui::Ui) + 'static,
{
    let options = eframe::NativeOptions::default();
    eframe::run_native(
        "Test App",
        options,
        Box::new(|_cc| Ok(Box::new(TestApp::new(f)))),
    )
    .unwrap();
}

struct TestApp<F>
where
    F: FnMut(&mut egui::Ui),
{
    f: F,
}

impl<F> TestApp<F>
where
    F: FnMut(&mut egui::Ui),
{
    fn new(f: F) -> Self {
        Self { f }
    }
}

impl<F> eframe::App for TestApp<F>
where
    F: FnMut(&mut egui::Ui),
{
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        egui::CentralPanel::default().show(ctx, |ui| {
            (self.f)(ui);
        });
    }
}
