pub mod dim2;
mod gallery;
mod specific;
pub mod text;

use self::{gallery::GalleryFigure, specific::SpecificFigure};
use crate::chart::{StandardChart, StandardChartDim0, StandardChartDim1};
#[cfg(feature = "egui")]
use egui::{pos2, Color32, Rect, Ui, Vec2};
use husky_figure_zone_protocol::FigureZone;
use husky_ki_repr_interface::KiReprInterface;
use husky_linket_impl::pedestal::{IsPedestal, IsPedestalFull, JointPedestal};
use husky_standard_linket_impl::pedestal::{StandardJointPedestal, StandardPedestal};
use husky_standard_linket_impl::var::StandardVarId;
use husky_trace_protocol::{
    chart::Chart,
    figure::{FigureUi, IsFigure},
    server::TracePlotInfos,
    trace_id::TraceId,
};
use husky_visual_protocol::visual::{
    shape::{Point, VisualRect},
    CompositeVisual,
};
use husky_visual_protocol::{
    synchrotron::VisualSynchrotron,
    visual::{
        image::ImageVisual,
        shape::{ShapeVisual, ShapeVisualData},
        Visual,
    },
};
use serde::{Deserialize, Serialize};
use text::TextFigure;
use ui::visual::cache::VisualUiCache;

#[enum_class::from_variants]
#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub enum StandardFigure {
    Void,
    Specific(SpecificFigure),
    Dim1(GalleryFigure),
    Text(TextFigure),
}

/// # impl IsFigure
impl IsFigure for StandardFigure {
    type Pedestal = StandardPedestal;

    fn for_all_joint_pedestals(&self, f: impl FnMut(&StandardJointPedestal)) {
        match self {
            StandardFigure::Void => (),
            StandardFigure::Specific(slf) => slf.for_all_joint_pedestals(f),
            StandardFigure::Dim1(slf) => slf.for_all_joint_pedestals(f),
            StandardFigure::Text(slf) => slf.for_all_joint_pedestals(f),
        }
    }

    fn new_void() -> Self {
        Self::Void
    }

    fn new_specific(
        chart: StandardChartDim0<CompositeVisual<TraceId>>,
        trace_plot_map: &TracePlotInfos,
        visual_synchrotron: &VisualSynchrotron,
    ) -> StandardFigure {
        SpecificFigure::from_chart(chart, trace_plot_map, visual_synchrotron).into()
    }

    fn new_gallery(
        chart: StandardChartDim1<CompositeVisual<TraceId>>,
        trace_plot_map: &TracePlotInfos,
        visual_synchrotron: &VisualSynchrotron,
    ) -> StandardFigure {
        GalleryFigure::from_chart(chart, trace_plot_map, visual_synchrotron).into()
    }

    fn new_text(
        chart: Option<StandardChartDim1<CompositeVisual<TraceId>>>,
        trace_plot_map: &TracePlotInfos,
        visual_synchrotron: &VisualSynchrotron,
    ) -> StandardFigure {
        todo!()
    }
}

#[cfg(feature = "egui")]
impl FigureUi<Ui> for StandardFigure {
    fn figure_ui(
        &self,
        visual_synchrotron: &VisualSynchrotron,
        cache: &mut VisualUiCache<Ui>,
        ui: &mut Ui,
    ) {
        match self {
            StandardFigure::Void => (),
            StandardFigure::Specific(slf) => slf.figure_ui(visual_synchrotron, cache, ui),
            StandardFigure::Dim1(slf) => slf.figure_ui(visual_synchrotron, cache, ui),
            StandardFigure::Text(text_figure) => todo!(),
        }
    }
}
