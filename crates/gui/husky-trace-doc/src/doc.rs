use crate::{view::TraceDocView, *};
#[cfg(feature = "egui")]
use egui::*;
use facade::TraceDocFacade;
use hotkey::TraceDocHotkeyAction;
use husky_gui::helpers::repaint_signal::EguiRepaintSignal;
use husky_trace_protocol::{
    caryatid::CaryatidUi,
    client::TraceClient,
    figure::FigureUi,
    protocol::{IsTraceProtocol, IsTraceProtocolFull},
    view::action::TraceViewActionBuffer,
};
use notify_change::NotifyChange;
use std::{path::PathBuf, sync::Arc};
use ui::{
    app::IsParentActionBuffer,
    component::ComponentUi,
    hotkey::egui::{HotkeyBuffer, HotkeyMap},
    visual::cache::VisualUiCache,
};

/// storage, state
pub struct TraceDoc<TraceProtocol, RepaintSignal>
where
    TraceProtocol: IsTraceProtocol,
    RepaintSignal: NotifyChange,
{
    current_dir: PathBuf,
    trace_client: TraceClient<TraceProtocol, RepaintSignal>,
    facade: TraceDocFacade,
    prev_facade: Option<TraceDocFacade>,
    view_action_buffer: TraceViewActionBuffer<TraceProtocol>,
    figure_ui_cache: ui::visual::cache::VisualUiCache<egui::Ui>,
    // set after client is initialized
    caryatid_ui_buffer: <TraceProtocol::Caryatid as IsCaryatid>::UiBuffer,
    hotkey_map: HotkeyMap<TraceDocHotkeyAction>,
}

impl<TraceProtocol: IsTraceProtocolFull> TraceDoc<TraceProtocol, EguiRepaintSignal> {
    pub fn new(
        tokio_runtime: Arc<tokio::runtime::Runtime>,
        server_address: impl Into<String>,
        repaint_signal: EguiRepaintSignal,
        _ctx: &egui::Context,
    ) -> Self {
        Self {
            current_dir: std::env::current_dir().unwrap(),
            trace_client: TraceClient::new(tokio_runtime, server_address, repaint_signal),
            facade: Default::default(),
            prev_facade: None,
            view_action_buffer: Default::default(),
            figure_ui_cache: Default::default(),
            caryatid_ui_buffer: Default::default(),
            hotkey_map: HotkeyMap::new([(
                "Alt+F",
                TraceDocHotkeyAction::FillCaryatidWithTraceVarDeps,
            )])
            .unwrap(),
        }
    }
}

#[cfg(feature = "egui")]
impl<TraceProtocol, ParentSettings, ParentActionBuffer>
    ComponentUi<egui::Ui, ParentSettings, ParentActionBuffer>
    for TraceDoc<TraceProtocol, EguiRepaintSignal>
where
    TraceProtocol: IsTraceProtocolFull,
    TraceProtocol::Figure: FigureUi<egui::Ui>,
    TraceProtocol::Caryatid: CaryatidUi<Ui>,
    ParentSettings: HasTraceDocSettings,
    ParentActionBuffer: IsParentActionBuffer,
{
    fn component_ui(
        &mut self,
        parent_settings: &mut ParentSettings,
        hotkey_buffer: &mut HotkeyBuffer,
        parent_action_buffer: &mut ParentActionBuffer,
        ui: &mut egui::Ui,
    ) {
        self.trace_client.update();
        if let Some((number, hotkey_action)) = hotkey_buffer.extract(&self.hotkey_map) {
            if let Some(view_action) =
                hotkey_action.view_action(number, self.trace_client.opt_trace_synchrotron())
            {
                self.view_action_buffer.push(view_action)
            } else {
                // todo: report invalid hotkey press
            }
        }
        self.render_inner(ui, parent_settings);
        let actions = self.view_action_buffer.take_actions(parent_action_buffer);
        if actions.len() > 1 {
            use husky_print_utils::p;
            p!(actions);
            todo!()
        }
        for action in actions {
            match self.trace_client.take_view_action(action) {
                Ok(_) => (),
                Err(e) => println!("e = {e} while take action"),
            }
        }
    }

    fn toggle_help_facade(&mut self) {
        if self.facade != TraceDocFacade::Help {
            assert!(self.prev_facade.is_none());
            self.prev_facade = Some(self.facade);
            self.facade = TraceDocFacade::Help;
        } else {
            self.facade = self.prev_facade.unwrap_or_default();
            self.prev_facade = None;
        }
    }
}

#[cfg(feature = "egui")]
impl<TraceProtocol> TraceDoc<TraceProtocol, EguiRepaintSignal>
where
    TraceProtocol: IsTraceProtocolFull,
    TraceProtocol::Figure: FigureUi<egui::Ui>,
    TraceProtocol::Caryatid: CaryatidUi<Ui>,
{
    fn render_inner<Settings>(&mut self, ui: &mut Ui, settings: &mut Settings)
    where
        Settings: HasTraceDocSettings,
    {
        let trace_client = &self.trace_client;
        if let Some(e) = trace_client.connection_error() {
            ui.label(RichText::new(e.to_string()).color(Color32::RED));
        }
        if let Some(trace_synchrotron) = trace_client.opt_trace_synchrotron() {
            TraceDocView::new(
                &self.current_dir,
                trace_synchrotron,
                &mut self.facade,
                &mut self.view_action_buffer,
                settings,
                &mut self.figure_ui_cache,
                &mut self.caryatid_ui_buffer,
                ui,
            )
            .facade_ui(ui);
        } else {
            // todo: render connecting status
        }
    }
}
