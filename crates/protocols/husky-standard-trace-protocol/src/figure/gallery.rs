use super::*;
use crate::chart::StandardChartDim1;
#[cfg(feature = "egui")]
use egui::{vec2, Frame, Sense};
use husky_standard_linket_impl::pedestal::StandardJointPedestal;
use ui::visual::cache::VisualUiCache;

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub struct GalleryFigure {
    specific_figures: Vec<SpecificFigure>,
}

/// # constructor
impl GalleryFigure {
    pub(super) fn from_chart(
        chart: StandardChartDim1<CompositeVisual<TraceId>>,
        trace_plot_map: &TracePlotInfos,
        visual_synchrotron: &VisualSynchrotron,
    ) -> Self {
        Self {
            specific_figures: chart
                .into_iter()
                .map(|chart_dim0| {
                    SpecificFigure::from_chart(chart_dim0, trace_plot_map, visual_synchrotron)
                })
                .collect(),
        }
    }
}

impl GalleryFigure {
    pub(super) fn for_all_joint_pedestals(&self, mut f: impl FnMut(&StandardJointPedestal)) {
        self.specific_figures
            .iter()
            .for_each(|figure| figure.for_all_joint_pedestals(&mut f))
    }
}

/// # ui
#[cfg(feature = "egui")]
impl GalleryFigure {
    pub(super) fn figure_ui(
        &self,
        visual_synchrotron: &VisualSynchrotron,
        cache: &mut ui::visual::cache::VisualUiCache<Ui>,
        ui: &mut Ui,
    ) {
        let num_rows = 7;
        let num_columns = 7;
        let grid_height = ui.available_height() / (num_rows as f32);
        let figure_height = grid_height.floor();
        let grid_width = ui.available_width() / (num_columns as f32);
        let figure_width = grid_width.floor();
        let base = ui.cursor().min;
        egui::Grid::new("generic_standard_figure")
            .num_columns(num_columns)
            .show(ui, |ui| {
                let num_rows = self.specific_figures.len() / num_columns
                    + if self.specific_figures.len() % num_columns == 0 {
                        0
                    } else {
                        1
                    };
                for i in 0..num_rows {
                    for j in 0..num_columns {
                        let index = i * num_columns + j;
                        if index < self.specific_figures.len() {
                            let rect = Rect::from_min_max(
                                base + vec2((i as f32) * grid_width, (j as f32) * grid_height),
                                base + vec2(
                                    ((i + 1) as f32) * grid_width,
                                    ((j + 1) as f32) * grid_height,
                                ),
                            );
                            ui.allocate_ui_at_rect(rect, |ui| {
                                self.specific_figures[index].figure_ui(
                                    visual_synchrotron,
                                    cache,
                                    ui,
                                )
                            });
                        }
                    }
                    ui.end_row()
                }
            });
    }
}
