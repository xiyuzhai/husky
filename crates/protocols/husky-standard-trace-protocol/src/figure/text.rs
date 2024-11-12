use super::*;
use husky_figure_zone_protocol::text::{FigureText, FigureTextId};

#[derive(Debug, PartialEq, Eq, Clone, Serialize, Deserialize)]
pub struct TextFigure {
    text: FigureTextId,
    specific_figures: Vec<SpecificFigure>,
}

impl TextFigure {
    pub(super) fn for_all_joint_pedestals(&self, mut f: impl FnMut(&StandardJointPedestal)) {
        // TODO ad hoc
        self.specific_figures
            .iter()
            .for_each(|figure| figure.for_all_joint_pedestals(&mut f))
    }
}
