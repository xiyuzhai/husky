use crate::*;
use doc::arena::DocId;

// TODO: more privacy
pub(crate) struct NotebookApp {
    pub(crate) dock_state: egui_dock::DockState<DocTab>,
    pub(crate) docs: Docs,
    pub(crate) settings: NotebookSettings,
    pub(crate) hotkey_buffer: HotkeyBuffer,
    pub(crate) action_buffer: NotebookActionBuffer,
    pub(crate) concentration: Option<DocId>,
    tokio_runtime: Arc<tokio::runtime::Runtime>,
    init_done: bool,
}

impl Default for NotebookApp {
    fn default() -> Self {
        let action_buffer = Default::default();
        let dock_state = egui_dock::DockState::new(vec![]);
        let docs = Docs::default();
        let settings = Default::default();
        Self {
            settings,
            dock_state,
            docs,
            hotkey_buffer: Default::default(),
            concentration: None,
            action_buffer,
            tokio_runtime: Arc::new(tokio::runtime::Runtime::new().unwrap()),
            init_done: false,
        }
    }
}

impl NotebookApp {
    pub(crate) fn tokio_runtime(&self) -> &Arc<tokio::runtime::Runtime> {
        &self.tokio_runtime
    }
}

impl eframe::App for NotebookApp {
    fn update(&mut self, ctx: &egui::Context, _frame: &mut eframe::Frame) {
        if !self.init_done {
            self.init(ctx);
            self.init_done = true;
        }
        self.hotkey_buffer.start_frame(ctx);
        if let Some((argument, action)) = self.hotkey_buffer.extract(self.settings.hotkey_map()) {
            let action = NotebookAction::from_hotkey_action(argument, action);
            self.take_action(action);
        }
        self.render_facade(ctx);
        for action in self.action_buffer.take_all() {
            self.take_action(action);
        }
    }
}

impl NotebookApp {
    fn init(&mut self, ctx: &egui::Context) {
        self.add_default_docs(ctx);
    }
}
