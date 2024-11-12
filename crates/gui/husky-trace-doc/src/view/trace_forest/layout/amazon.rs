use super::*;
use egui::{Frame, Separator};
use husky_value::ki_control_flow::KiControlFlow;

impl<'a, TraceProtocol, Settings> TraceDocView<'a, TraceProtocol, Settings>
where
    TraceProtocol: IsTraceProtocol,
    TraceProtocol::Figure: FigureUi<egui::Ui>,
    Settings: HasTraceDocSettings,
{
    pub(super) fn amazon_trace_forest_ui(&mut self, ui: &mut egui::Ui) {
        Frame::none().inner_margin(CONSTANT1).show(ui, |ui| {
            ui.vertical(|ui| {
                ui.style_mut().spacing.item_spacing = vec2(CONSTANT1, CONSTANT1);
                self.render_bundles(ui);
                ui.allocate_space(ui.available_size())
            })
        });
    }

    fn render_bundles(&mut self, ui: &mut egui::Ui) {
        for trace_bundle in self.trace_synchrotron.trace_id_bundles() {
            self.render_bundle(ui, trace_bundle);
        }
    }

    fn render_bundle(&mut self, ui: &mut egui::Ui, trace_bundle: &TraceIdBundle) {
        Frame::none()
            .inner_margin(0.0)
            .stroke((0.5, Color32::GRAY))
            .rounding(4.0)
            .show(ui, |ui| self.render_bundle_inner(trace_bundle, ui));
    }

    fn render_bundle_inner(&mut self, trace_bundle: &TraceIdBundle, ui: &mut egui::Ui) {
        ui.style_mut().spacing.item_spacing = vec2(0.0, 1.0);
        Frame::none()
            .inner_margin(Margin {
                left: 6.0,
                right: 6.0,
                top: 2.0,
                bottom: 2.0,
            })
            .show(ui, |ui| {
                ui.horizontal(|ui| {
                    ui.label(
                        RichText::new(format!(
                            "{}",
                            pathdiff::diff_paths(
                                trace_bundle.crate_root_module_file_abs_path(),
                                self.current_dir
                            )
                            .unwrap()
                            .display()
                        ))
                        .color(Color32::GREEN),
                    )
                })
            });
        Separator::default().spacing(1.0).ui(ui);
        Frame::none()
            .inner_margin(Margin {
                left: 4.0,
                right: 4.0,
                top: 0.0,
                bottom: 6.0,
            })
            .show(ui, |ui| {
                self.render_traces(trace_bundle.root_trace_ids(), ui)
            });
    }

    #[cfg(feature = "egui")]
    fn render_traces(&mut self, trace_ids: &[TraceId], ui: &mut egui::Ui) {
        ui.allocate_at_least(Vec2::new(ui.available_width(), 0.), Sense::hover());
        ui.vertical(|ui| {
            for &trace_id in trace_ids {
                self.render_trace_view_tree(trace_id, ui)
            }
        });
    }

    fn render_trace_view_tree(&mut self, trace_id: TraceId, ui: &mut egui::Ui)
    where
        TraceProtocol: IsTraceProtocol,
    {
        let caryatid = self.trace_synchrotron.caryatid();
        let entry = &self.trace_synchrotron[trace_id];
        self.render_trace_view(caryatid.pedestal(entry.var_deps()), trace_id, entry, ui);
        if entry.expanded()
            && let Some(subtrace_ids) = entry.subtrace_ids()
        {
            self.render_subtraces(ui, entry.view_data().trace_kind, subtrace_ids);
        }
        for &assoc_trace_id in entry.assoc_trace_ids() {
            self.render_assoc_trace(assoc_trace_id, ui)
        }
    }

    fn render_trace_view(
        &mut self,
        pedestal: Option<<TraceProtocol as IsTraceProtocol>::Pedestal>,
        trace_id: TraceId,
        entry: &TraceSynchrotronEntry<TraceProtocol>,
        ui: &mut egui::Ui,
    ) where
        TraceProtocol: IsTraceProtocol,
    {
        let trace_view_inner_margin: Margin = Margin {
            left: 5.0,
            right: 5.0,
            top: 0.0,
            bottom: 0.0,
        };
        // todo: consider multiline value representation
        let desired_space = Vec2::new(
            ui.available_width(),
            // todo: consider multiline
            trace_view_inner_margin.top
                + ui.style().spacing.interact_size.y
                    * (entry.view_data().lines_data().len() as f32)
                + trace_view_inner_margin.bottom,
        );
        let desired_rect = egui::Rect {
            min: ui.cursor().min,
            max: ui.cursor().min + desired_space,
        };
        let trace_view_response = &ui.interact(desired_rect, ui.next_auto_id(), Sense::click());
        let followed = self.trace_synchrotron.followed() == Some(trace_id);
        // `hovered_within` tells if the pointer is within the trace view
        // we don't use hover because we don't want widgets to intercept
        let hovered_within = ui.rect_contains_pointer(trace_view_response.rect);
        if !followed {
            let follow = trace_view_response.clicked();
            if follow {
                self.add_action(TraceViewAction::FollowTrace { followed: trace_id })
            }
        }
        let mut frame = Frame::none()
            .inner_margin(trace_view_inner_margin)
            .rounding(3.0);
        if hovered_within || followed {
            frame.stroke.color = if !followed {
                frame.stroke.width = 1.0;
                Color32::from_rgb(55, 55, 0)
            } else {
                frame.stroke.width = 1.0;
                Color32::GOLD
            }
        }
        let _response = frame
            .show(ui, |ui| {
                ui.horizontal(|ui| {
                    ui.spacing_mut().item_spacing.x = 2.;
                    let accompanied = self.trace_synchrotron.accompanied(trace_id);
                    self.render_accompany_toggler(trace_id, accompanied, ui);
                    self.render_expansion_toggler(
                        trace_id,
                        entry.view_data().have_subtraces(),
                        entry.expanded(),
                        ui,
                    );
                    ui.spacing_mut().item_spacing.x = 0.;
                    ui.vertical(|ui| {
                        let lines_data = entry.view_data().lines_data();
                        for line_data in &lines_data[..(lines_data.len() - 1)] {
                            ui.horizontal(|ui| self.render_line(line_data, trace_id, entry, ui));
                        }
                        ui.horizontal(|ui| {
                            self.render_line(lines_data.last().unwrap(), trace_id, entry, ui);
                            if let Some(pedestal) = pedestal {
                                match entry
                                    .stalk(&pedestal)
                                    .value_presentation_control_flow_result()
                                {
                                    Ok(Some(value_presentation_control_flow)) => {
                                        match value_presentation_control_flow {
                                            KiControlFlow::Continue(value) => {
                                                self.render_value(value, ui)
                                            }
                                            KiControlFlow::LoopContinue => {
                                                ui.label("loop continue");
                                            }
                                            KiControlFlow::LoopExit(_) => {
                                                ui.label("loop exit");
                                            }
                                            KiControlFlow::Return(value) => {
                                                self.render_space_chars(1, ui);
                                                ui.label(
                                                    RichText::new("return")
                                                        .color(::egui::Color32::BLUE),
                                                );
                                                self.render_value(value, ui)
                                            }
                                            KiControlFlow::Undefined => {
                                                ui.label("undefined");
                                            }
                                            KiControlFlow::Throw(value) => {
                                                self.render_space_chars(1, ui);
                                                ui.label(
                                                    RichText::new("throw")
                                                        .color(::egui::Color32::BLUE),
                                                );
                                                self.render_value(value, ui)
                                            }
                                        }
                                    }
                                    Ok(None) => (),
                                    Err(_) => todo!(),
                                }
                            }
                            // this is important to keep the interaction region large enough
                            let desired_size = ui.available_size() - Vec2::new(1.0, 0.0);
                            if desired_size.x > 0.0 && desired_size.y > 0.0 {
                                ui.allocate_space(desired_size);
                            }
                        });
                    })
                })
            })
            .response;
    }

    fn render_subtraces(
        &mut self,
        ui: &mut egui::Ui,
        trace_kind: TraceKind,
        subtrace_ids: &[TraceId],
    ) {
        match trace_kind {
            TraceKind::Submodule => {
                Frame::none()
                    .inner_margin(Margin {
                        left: 2.0,
                        right: 2.0,
                        top: 0.0,
                        bottom: 0.0,
                    })
                    .stroke((0.5, Color32::LIGHT_GRAY))
                    .rounding(4.0)
                    .show(ui, |ui| {
                        Frame::none()
                            .inner_margin(1.)
                            .show(ui, |ui| self.render_traces(subtrace_ids, ui))
                    });
            }
            TraceKind::EagerPattern => todo!(),
            TraceKind::StaticVar => unreachable!("no subtraces"),
            TraceKind::Val => {
                Frame::none()
                    .inner_margin(0.)
                    .show(ui, |ui| self.render_traces(subtrace_ids, ui));
            }
            TraceKind::LazyCall => todo!(),
            TraceKind::LazyCallInput => todo!(),
            TraceKind::LazyExpr => todo!(),
            TraceKind::LazyPattern => todo!(),
            TraceKind::LazyStmt => {
                self.render_traces(subtrace_ids, ui);
            }
            TraceKind::EagerCall => todo!(),
            TraceKind::EagerExpr => todo!(),
            TraceKind::EagerStmt => {
                self.render_traces(subtrace_ids, ui);
            }
            TraceKind::EagerCallInput => todo!(),
            TraceKind::Value => todo!(),
            TraceKind::Repl => todo!(),
            TraceKind::LazyLoopFrame => todo!(),
            TraceKind::LazyLoopRange => todo!(),
            TraceKind::EagerLoopFrame => todo!(),
            TraceKind::EagerLoopRange => todo!(),
        }
    }

    fn render_assoc_trace(&mut self, assoc_trace_id: TraceId, ui: &mut egui::Ui) {
        Frame::none().inner_margin(3.0).show(ui, |ui| {
            Frame::none().show(ui, |ui| {
                ui.spacing_mut().item_spacing.y = 0.;
                ui.allocate_space(Vec2::new(ui.available_width(), 0.));
                self.render_trace_view_tree(assoc_trace_id, ui);
            })
        });
    }

    fn render_line(
        &mut self,
        line_data: &TraceViewLineData,
        trace_id: TraceId,
        entry: &TraceSynchrotronEntry<TraceProtocol>,
        ui: &mut egui::Ui,
    ) {
        for token_data in line_data.tokens_data() {
            self.render_token(token_data, trace_id, entry, ui);
        }
    }
}
